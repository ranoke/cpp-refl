#include <stdio.h>

#include <map>
#include <vector>
#include <string>
#include <cassert>
#include <type_traits>

#include <stdint.h>

#define REFL_TO_STRING(x) #x
#define REFL_ARRAY_SIZE(array) ((sizeof(array)/sizeof(array[0])))
#define REFL_OFFSET_OF(type, member) ((size_t)(&(((type*)(nullptr))->member)))
#define REFL_TYPE_OF(type, member) refl::_get_refl_type<decltype(type::member)>()
#define REFL_CUSTOM_OF(type, member) refl::_get_custom_refl<decltype(type::member)>()

#define REFL_PARENS ()

#define REFL_EXPAND(...) REFL_EXPAND4(REFL_EXPAND4(REFL_EXPAND4(REFL_EXPAND4(__VA_ARGS__))))
#define REFL_EXPAND4(...) REFL_EXPAND3(REFL_EXPAND3(REFL_EXPAND3(REFL_EXPAND3(__VA_ARGS__))))
#define REFL_EXPAND3(...) REFL_EXPAND2(REFL_EXPAND2(REFL_EXPAND2(REFL_EXPAND2(__VA_ARGS__))))
#define REFL_EXPAND2(...) REFL_EXPAND1(REFL_EXPAND1(REFL_EXPAND1(REFL_EXPAND1(__VA_ARGS__))))
#define REFL_EXPAND1(...) __VA_ARGS__

#define REFL_FOR_EACH(macro, ...)                                    \
  __VA_OPT__(REFL_EXPAND(REFL_FOR_EACH_HELPER(macro, __VA_ARGS__)))
#define REFL_FOR_EACH_HELPER(macro, a1, ...)                         \
  macro(a1)                                                          \
  __VA_OPT__(REFL_FOR_EACH_AGAIN REFL_PARENS (macro, __VA_ARGS__))
#define REFL_FOR_EACH_AGAIN() REFL_FOR_EACH_HELPER

#define REFL_FOR_EACH_CTX(macro, ctx, ...)                                    \
  __VA_OPT__(REFL_EXPAND(REFL_FOR_EACH_HELPER_CTX(macro, ctx, __VA_ARGS__)))
#define REFL_FOR_EACH_HELPER_CTX(macro, ctx, a1, ...)                         \
  macro(ctx, a1)                                                              \
  __VA_OPT__(REFL_FOR_EACH_AGAIN_CTX REFL_PARENS (macro, ctx, __VA_ARGS__))
#define REFL_FOR_EACH_AGAIN_CTX() REFL_FOR_EACH_HELPER_CTX

#define REFL_TYPE_REGISTER(type, ret)              \
    template<>                                     \
    constexpr ReflTypeE _get_refl_type<type>()     \
    {                                              \
        return ret;                                \
    }

#define REFL_DEF_MEMBER(obj, name) { REFL_TO_STRING(name), REFL_OFFSET_OF(obj, name), REFL_TYPE_OF(obj, name), REFL_CUSTOM_OF(obj, name) },
#define _REFL_DEF_MEMBERS(obj, ...)                          \
    static refl::ReflMember members[] = {                    \
        REFL_FOR_EACH_CTX(REFL_DEF_MEMBER, obj, __VA_ARGS__) \
    }

#define _REFL_DEF_REFLECTION(obj)                  \
    static auto r = (refl::Refl){                  \
        .name = REFL_TO_STRING(obj),               \
        .members = members,                        \
        .members_count = REFL_ARRAY_SIZE(members), \
    }

#define REFL_DEF(name, ...)                   \
    static refl::Refl* _get_refl()            \
    {                                         \
        _REFL_DEF_MEMBERS(name, __VA_ARGS__); \
        _REFL_DEF_REFLECTION(name);           \
        return &r;                            \
    }

namespace refl
{
    enum ReflTypeE
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
        REFL_TYPE_STD_VECTOR,
        REFL_TYPE_STD_MAP,
        _REFL_TYPE_COUNT,
    };

    enum ReflCustomE
    {
        REFL_CUSTOM_NONE,
        REFL_CUSTOM_OBJ,
        REFL_CUSTOM_VECTOR,
        REFL_CUSTOM_MAP,
        _REFL_CUSTOM_COUNT,
    };

    struct Refl;
    struct ReflCustomObj;
    struct ReflCustomVector;
    struct ReflCustomMap;

    struct ReflCustom
    {
        void* custom_refl;
        ReflCustomE refl_type;
    };

    struct ReflCustomObj
    {
        Refl* refl;
    };

    struct ReflCustomVector
    {
        ReflTypeE container_type;
        ReflCustom* container_refl;
    };

    struct ReflCustomMap
    {
        ReflTypeE container_key_type;
        ReflCustom* container_key_custom_refl;
        ReflTypeE container_value_type;
        ReflCustom* container_value_custom_refl;
    };

    struct ReflMember
    {
        const char* name;
        size_t offset;
        ReflTypeE type;
        ReflCustom* custom_refl;
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
    constexpr ReflTypeE _get_refl_type()
    {
        if constexpr (std::is_class<T>::value)
        {
            // static_assert(HasRefl<T>::value); // causing trouble with std::map?
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

    template<typename T>
    constexpr ReflTypeE _get_refl_type(std::vector<T>*)
    {
        return REFL_TYPE_STD_VECTOR;
    }

    template<typename K, typename V>
    constexpr ReflTypeE _get_refl_type(std::map<K, V>*)
    {
        return REFL_TYPE_STD_MAP;
    }

    template<typename T>
    constexpr Refl* _get_obj_refl();

    template<typename T>
    Refl* _get_obj_refl_helper(std::vector<T>)
    {
        // we do not know the name - there is no need ?
        // we do not know the offset - it is private field
        // that filed is just a pointer to a data(array)
        static ReflMember members[] = {
            { "", 0, _get_refl_type<T>() },
        };
        static Refl* objects[] = {
            refl::_get_obj_refl<T>(),
        };
        static auto r = (Refl){
            .name = "",
            .members = members,
            .members_count = 1,
        };
        return &r;
    }

    template<typename K, typename V>
    Refl* _get_obj_refl_helper(std::map<K, V>)
    {
        static ReflMember members[] = {
            { "key", 0, _get_refl_type<K>() },
            { "value", 0, _get_refl_type<V>() },
        };
        static Refl* objects[] = {
            refl::_get_obj_refl<K>(),
            refl::_get_obj_refl<V>(),
        };
        static auto r = (Refl){
            .name = "",
            .members = members,
            .members_count = 2,
        };
        return &r;
    }

    template<typename T>
    constexpr Refl* _get_obj_refl()
    {
        // TODO ignore types like std::string
        if constexpr (std::is_class<T>::value && HasRefl<T>::value)
            return T::_get_refl();
        else if constexpr (std::is_class<T>::value)
            return _get_obj_refl_helper(T{});
        else
            return nullptr; // not an object
    }

    template<typename T>
    constexpr ReflCustom* _get_custom_refl()
    {
        return nullptr;
    }

} // namespace refl

struct SomeObj
{
    int32_t val;
    const char* text;

    REFL_DEF(SomeObj, val, text);
};

struct Name
{
    const char* name_xd;
    uint64_t uid;

    SomeObj obj;

    REFL_DEF(Name, name_xd, uid, obj);
};

struct Vec3
{
    float x, y, z;
    double b;

    int16_t bit16;
    Name name;

    REFL_DEF(Vec3, x, y, z, b, bit16, name);
};

struct Arr
{
    std::vector<std::vector<Name>> vals;
    Vec3 vec;

    Name name;

    REFL_DEF(Arr, vals, vec, name);
};

struct Mapping
{
    std::map<const char*, Name> m;

    REFL_DEF(Mapping, m);
};

/*
    {
        "Arr": {
            "vals": {1, 2, 3}
        }
    }
 */

/* void print_refl(refl::Refl reflection); */

/* void print_refl_vector(refl::Refl reflection) */
/* { */
/*     printf("{\n\t\t\"std::vector<%d>\":", reflection.members[0].type); */
/*     if (reflection.objects[0]) */
/*         print_refl_vector(*reflection.objects[0]); */
/*     else */
/*     { */
/*         printf("{}"); */
/*     } */
/*     printf("}\n"); */
/* } */

/* void print_refl_map(refl::Refl reflection) */
/* { */
/*     printf("{\n\t\t\"std::map<%d, %d>\":", reflection.members[0].type, reflection.members[1].type); */
/*     if (reflection.objects[0] && reflection.objects[1]) */
/*     { */
/*         print_refl(*reflection.object); */
/*         print_refl(*reflection.object); */
/*     } */
/*     else if (reflection.objects[0]) */
/*     { */
/*         print_refl(*reflection.objects[0]); */
/*         printf("{} "); */
/*     } */
/*     else if (reflection.objects[1]) */
/*     { */
/*         printf("{} "); */
/*         print_refl(*reflection.objects[1]); */
/*     } */
/*     else */
/*     { */
/*         printf("{} "); */
/*         printf("{} "); */
/*     } */
/*     printf("}\n"); */
/* } */

void print_refl(refl::Refl reflection)
{
    printf("\t\"%s\": {\n", reflection.name);
    for (size_t i = 0; i < reflection.members_count; i++)
    {
        if (reflection.members[i].type == refl::REFL_TYPE_STD_VECTOR)
        {
            /* print_refl_vector(*reflection.objects[i]); */
        }
        else if (reflection.members[i].type == refl::REFL_TYPE_STD_MAP)
        {
            /* print_refl_map(*reflection.objects[i]); */
        }
        else if (reflection.members[i].type == refl::REFL_TYPE_OBJ)
        {
            /* auto ref = *reflection.objects[i]; */
            /* print_refl(ref); */
        }
        else
        {
            printf("\t\t{ \"%s\", %d },\n", reflection.members[i].name, reflection.members[i].type);
        }
    }
    printf("\t}\n");
}


int main()
{
    //auto reflection = *refl::_get_obj_refl<decltype(Vec3::name)>();

    auto reflection = *Vec3::_get_refl();

    /* auto reflection = *Arr::_get_refl(); */
    printf("{\n");
    print_refl(reflection);
    printf("}\n");

    return 0;

    /* reflection = *Vec3::_get_refl(); */
    /* printf("{\n\t\"%s\": {\n", reflection.name); */
    /* for (size_t i = 0; i < reflection.members_count; i++) */
    /* { */
    /*     printf("\t\t{ \"%s\", %d },\n", reflection.members[i].name, reflection.members[i].type); */
    /* } */
    /* printf("\t}\n}\n"); */

    /* reflection = *Name::_get_refl(); */
    /* printf("{\n\t\"%s\": {\n", reflection.name); */
    /* for (size_t i = 0; i < reflection.members_count; i++) */
    /* { */
    /*     printf("\t\t{ \"%s\", %d },\n", reflection.members[i].name, reflection.members[i].type); */
    /* } */
    /* printf("\t}\n}\n"); */

    /* return 0; */
}


