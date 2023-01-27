#include <stdio.h>

#include <string>
#include <cassert>
#include <type_traits>

#include <stdint.h>

#define REFL_TO_STRING(x) #x
#define REFL_ARRAY_SIZE(array) ((sizeof(array)/sizeof(array[0])))
#define REFL_OFFSET_OF(type, member) ((size_t)(&(((type*)(nullptr))->member)))
#define REFL_TYPE_OF(type, member) refl::get_refl_type(((&(((type*)(nullptr))->member))))

#define REFL_PARENS ()

#define REFL_EXPAND(...) REFL_EXPAND4(REFL_EXPAND4(REFL_EXPAND4(REFL_EXPAND4(__VA_ARGS__))))
#define REFL_EXPAND4(...) REFL_EXPAND3(REFL_EXPAND3(REFL_EXPAND3(REFL_EXPAND3(__VA_ARGS__))))
#define REFL_EXPAND3(...) REFL_EXPAND2(REFL_EXPAND2(REFL_EXPAND2(REFL_EXPAND2(__VA_ARGS__))))
#define REFL_EXPAND2(...) REFL_EXPAND1(REFL_EXPAND1(REFL_EXPAND1(REFL_EXPAND1(__VA_ARGS__))))
#define REFL_EXPAND1(...) __VA_ARGS__

#define REFL_FOR_EACH(macro, ...)                                    \
  __VA_OPT__(REFL_EXPAND(REFL_FOR_EACH_HELPER(macro, __VA_ARGS__)))
#define REFL_FOR_EACH_HELPER(macro, a1, ...)                         \
  macro(a1)                                                     \
  __VA_OPT__(REFL_FOR_EACH_AGAIN REFL_PARENS (macro, __VA_ARGS__))
#define REFL_FOR_EACH_AGAIN() REFL_FOR_EACH_HELPER

#define REFL_FOR_EACH_CTX(macro, ctx, ...)                                    \
  __VA_OPT__(REFL_EXPAND(REFL_FOR_EACH_HELPER_CTX(macro, ctx, __VA_ARGS__)))
#define REFL_FOR_EACH_HELPER_CTX(macro, ctx, a1, ...)                         \
  macro(ctx, a1)                                                     \
  __VA_OPT__(REFL_FOR_EACH_AGAIN_CTX REFL_PARENS (macro, ctx, __VA_ARGS__))
#define REFL_FOR_EACH_AGAIN_CTX() REFL_FOR_EACH_HELPER_CTX

#define REFL_TYPE_REGISTER(type, ret)             \
    template<>                                    \
    constexpr ReflType get_refl_type<type>(type*) \
    {                                             \
        return ret;                               \
    }

#define REFL_DEF_MEMBER(obj, name) { REFL_TO_STRING(name), REFL_OFFSET_OF(obj, name), REFL_TYPE_OF(obj, name) },

#define _REFL_DEF_MEMBERS(obj, ...)                          \
    static refl::ReflMember members[] = {                    \
        REFL_FOR_EACH_CTX(REFL_DEF_MEMBER, obj, __VA_ARGS__) \
    }

#define _REFL_RET_REFLECTION(obj)                  \
    return (refl::Refl){                           \
        .name = REFL_TO_STRING(obj),               \
        .members = members,                        \
        .members_count = REFL_ARRAY_SIZE(members), \
    }

#define REFL_DEF(name, ...)                   \
    static refl::Refl _get_refl()             \
    {                                         \
        _REFL_DEF_MEMBERS(name, __VA_ARGS__); \
        _REFL_RET_REFLECTION(name);           \
    }

namespace refl
{
    enum ReflType
    {
        REFL_TYPE_NONE,
        REFL_TYPE_OBJ,
        REFL_TYPE_STR,
        REFL_TYPE_STD_STR,
        REFL_TYPE_U8,
        REFL_TYPE_I8,
        REFL_TYPE_U16,
        REFL_TYPE_I16,
        REFL_TYPE_U32,
        REFL_TYPE_I32,
        REFL_TYPE_U64,
        REFL_TYPE_I64,
        REFL_TYPE_FLOAT,
        REFL_TYPE_DOUBLE,
    };

    struct ReflMember
    {
        const char* name;
        size_t offset;
        ReflType type;
    };

    struct Refl
    {
        const char* name;
        ReflMember* members;
        size_t members_count;
    };


    template<typename T, typename = int>
    struct HasRefl : std::false_type {};

    template<typename T>
    struct HasRefl <T, decltype((void) T::_get_refl, 0)> : std::true_type {};

    template<typename T>
    constexpr ReflType get_refl_type(T*)
    {
        if constexpr (std::is_class<T>::value)
        {
            static_assert(HasRefl<T>::value);
            return REFL_TYPE_OBJ;
        }
        assert(false && "Debug");
        return REFL_TYPE_NONE;
    }

    REFL_TYPE_REGISTER(uint8_t,     REFL_TYPE_U8);
    REFL_TYPE_REGISTER(int8_t,      REFL_TYPE_I8);
    REFL_TYPE_REGISTER(uint16_t,    REFL_TYPE_U16);
    REFL_TYPE_REGISTER(int16_t,     REFL_TYPE_I16);
    REFL_TYPE_REGISTER(uint32_t,    REFL_TYPE_U32);
    REFL_TYPE_REGISTER(int32_t,     REFL_TYPE_I32);
    REFL_TYPE_REGISTER(uint64_t,    REFL_TYPE_U64);
    REFL_TYPE_REGISTER(int64_t,     REFL_TYPE_I64);
    REFL_TYPE_REGISTER(const char*, REFL_TYPE_STR);
    REFL_TYPE_REGISTER(float,       REFL_TYPE_FLOAT);
    REFL_TYPE_REGISTER(double,      REFL_TYPE_DOUBLE);
    REFL_TYPE_REGISTER(std::string, REFL_TYPE_STD_STR);

} // namespace refl

struct Name
{
    uint32_t uid;
    const char* some_str;
    std::string std_str;
    uint8_t v;

    REFL_DEF(Name, uid, some_str, v, std_str);
};

struct Vec3
{
    float x, y, z;
    Name name;
    double b;

    int16_t bit16;

    REFL_DEF(Vec3, x, y, z, name, b, bit16);
};

int main()
{
    auto reflection = Vec3::_get_refl();
    printf("{\n\t\"%s\": {\n", reflection.name);
    for (size_t i = 0; i < reflection.members_count; i++)
    {
        printf("\t\t{ \"%s\", %d },\n", reflection.members[i].name, reflection.members[i].type);
    }
    printf("\t}\n}\n");

    reflection = Name::_get_refl();
    printf("{\n\t\"%s\": {\n", reflection.name);
    for (size_t i = 0; i < reflection.members_count; i++)
    {
        printf("\t\t{ \"%s\", %d },\n", reflection.members[i].name, reflection.members[i].type);
    }
    printf("\t}\n}\n");

    return 0;
}


