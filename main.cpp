#include <iostream>
#include <exception>
#include <string>
#include <vector>
#include <algorithm>
#include <cassert>
#include <sstream>
#include <iomanip>
#include <fstream>
#include <deque>
//#include <filesystem>
//namespace fs = std::filesystem;

using std::vector;

uint32_t rotr(const uint32_t& x, size_t n) {
    n %= 32;
    return (x >> n) | (x << (32 - n));
}

uint32_t rotl(const uint32_t& x, size_t n) {
    n %= 32;
    return (x << n) | (x >> (32 - n));
}

uint32_t ch(uint32_t x, uint32_t y, uint32_t z) {
    return (x & y) ^ (~x & z);
}

uint32_t maj(uint32_t x, uint32_t y, uint32_t z) {
    return (x & y) ^ (x & z) ^ (y & z);
}

uint32_t bigSigma_0_256(const uint32_t& x) {
    return rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22);
}

uint32_t bigSigma_1_256(const uint32_t& x) {
    return rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25);
}

uint32_t sigma_0_256(const uint32_t& x) {
    return rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3);
}

uint32_t sigma_1_256(const uint32_t& x) {
    return rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10);
}

using RoundStat = vector<vector<uint32_t>>;

std::string sha256(const std::string& mes, RoundStat& stat) {
    vector<uint8_t> vec;
    std::transform(mes.begin(), mes.end(), std::back_inserter(vec), [](char c) -> uint8_t {
        return static_cast<uint8_t>(c);
    });
    vec.push_back(0x80);
    while (448 != (vec.size() * 8) % 512) {
        vec.push_back(0x00);
    }
    uint64_t l = mes.length() * 8; // исходная длина сообщения в битах
    for (int i = 7; i >= 0; --i) {
        vec.push_back(static_cast<uint8_t>(l >> (i * 8)));
    }

    assert((vec.size() * 8) % 512 == 0);

    vector<vector<uint32_t>> blocks;
    vector<uint32_t> words;

    for (vector<uint8_t>::size_type i = 0; i < vec.size(); i += 4) {
        uint32_t M = 0x0;
        for (int j = 3; j >= 0; --j) {
            vector<uint8_t>::size_type offset = 3 - j + i;
            uint8_t wordPart = vec[offset];
            M |= wordPart << (j * 8);
        }
        words.push_back(M);
        if (words.size() == 16) {
            blocks.push_back(words);
            words.clear();
        }
    }

    const vector<uint32_t> K256 = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    };

    auto N = blocks.size();
    vector<vector<uint32_t>> H(N + 1);
    for (auto& hk : H) {
        hk.resize(8);
    }
    H[0][0] = 0x6a09e667; H[0][1] = 0xbb67ae85; H[0][2] = 0x3c6ef372; H[0][3] = 0xa54ff53a;
    H[0][4] = 0x510e527f; H[0][5] = 0x9b05688c; H[0][6] = 0x1f83d9ab; H[0][7] = 0x5be0cd19;

    for (auto i = 1; i <= N; ++i) {
        // 1. Подготовка списка преобразованных слов сообщения
        vector<uint32_t> W(64);
        for (int t = 0; t <= 15; ++t) {
            W[t] = blocks[i - 1][t];
        }
        for (int t = 16; t <= 63; ++t) {
            W[t] = sigma_1_256(W[t - 2]) + W[t - 7] + sigma_0_256(W[t - 15]) + W[t - 16];
        }

        // 2. Инициализация рабочих переменных
        uint32_t a = H[i - 1][0], b = H[i - 1][1], c = H[i - 1][2], d = H[i - 1][3],
                 e = H[i - 1][4], f = H[i - 1][5], g = H[i - 1][6], h = H[i - 1][7];

        // 3. Внутренний цикл
        for (int t = 0; t <= 63; ++t) {
            uint32_t T1 = h + bigSigma_1_256(e) + ch(e, f, g) + K256[t] + W[t];
            uint32_t T2 = bigSigma_0_256(a) + maj(a, b, c);
            h = g;
            g = f;
            f = e;
            e = d + T1;
            d = c;
            c = b;
            b = a;
            a = T1 + T2;

            // собираем статистику
            stat.push_back({a, b, c, d, e, f, g, h});
        }

        // 4. Вычисление промежуточного значения хэш-функции
        H[i][0] = a + H[i - 1][0]; H[i][1] = b + H[i - 1][1]; H[i][2] = c + H[i - 1][2]; H[i][3] = d + H[i - 1][3];
        H[i][4] = e + H[i - 1][4]; H[i][5] = f + H[i - 1][5]; H[i][6] = g + H[i - 1][6]; H[i][7] = h + H[i - 1][7];

        // статистика
        stat.push_back({ H[i][0], H[i][1], H[i][2], H[i][3], H[i][4], H[i][5], H[i][6], H[i][7] });
    }

    std::ostringstream oss;
    oss << std::hex << std::setfill('0');
    for (int i = 0; i < 8; ++i) {
        oss << std::setw(8) << H[N][i];
    }

    return oss.str();
}

std::string sha256(const std::string& mes) {
    RoundStat dummy;
    return sha256(mes, dummy);
}

std::string format32(const std::string& in) {
    std::ostringstream oss;
    int count = 0;
    for (const char& c : in) {
        oss << c;
        count++;
        if (count % 8 == 0) {
            oss << ' ';
        }
    }
    return oss.str();
}

std::deque<int> avalanche(const RoundStat& stat1, const RoundStat& stat2) {
    std::deque<int> result;
    size_t minSize = std::min(stat1.size(), stat2.size());
    for (size_t i = 0; i < minSize; ++i) {
        int roundDiff = 0;
        size_t wordCount = stat1[i].size();
        for (size_t j = 0; j < wordCount; ++j) {
            uint32_t wordXor = stat1[i][j] ^ stat2[i][j];
            uint32_t mask = 0x1;
            for (size_t k = 0; k < sizeof(wordXor)*8; ++k) {
                if (wordXor & (mask << k)) {
                    roundDiff++;
                }
            }
        }
        result.push_back(roundDiff);
    }
    return result;
}

std::string changeBit(std::string s, size_t n) {
    size_t bitPerChar = sizeof(std::string::value_type) * 8;
    assert(bitPerChar == 8);
    size_t charNum = n / bitPerChar;
    char& c = s.at(charNum);
    c ^= (0x80 >> (n % bitPerChar));
    return s;
}

int main()
try {
    vector<std::string> messages{"", "abc", "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"};
    for (const auto& m : messages) {
        std::cout << "sha256(\"" << m << "\") = \n" << format32(sha256(m)) << "\n\n";
    }
//    std::cout << "Enter string to hash: \n";
//    std::string s;
//    std::getline(std::cin, s);
//    std::cout << "sha256(\"" << s << "\") = " << format32(sha256(s));
//    std::cout << "Current path is " << fs::current_path() << '\n';

    std::ifstream ifs("in.txt");
    if (!ifs) {
        throw std::runtime_error("error opening input file");
    }
    std::stringstream buffer;
    buffer << ifs.rdbuf();
    std::string str = buffer.str();
    RoundStat stat1, stat2;
    std::string hash = sha256(str, stat1);
    std::cout << "sha256(\"" << str << "\") = \n" << hash << '\n';
    std::ofstream ofs("out.txt");
    if (!ofs) {
        throw std::runtime_error("error opening output file");
    }
    ofs << hash;

    std::cout << '"' << str << "\" has length " << str.size()*8 << " bit. Enter bit number to change [0 - " << str.size()*8-1 << "]\n";
    size_t n;
    std::cin >> n;
    std::string changedStr = changeBit(str, n);
    std::cout << "Original string: " << str << '\n';
    std::cout << "Changed  string: " << changedStr << '\n';
    std::string changedHash = sha256(changedStr, stat2);
    std::deque<int> bitDiff = avalanche(stat1, stat2);
    bitDiff.push_front(1);
    auto print = [](const int& n) { std::cout << n << " "; };
    std::cout << "Changed string hash:\n" << changedHash << '\n' << "Bits changed per round:\n";
    std::for_each(bitDiff.cbegin(), bitDiff.cend(), print);
    std::cout << '\n';

    return 0;
}
catch (const std::exception& e) {
    std::cerr << "Exception: " << e.what() << '\n';
    return 1;
}
catch (...) {
    std::cerr << "Unknown exception\n";
    return 2;
}