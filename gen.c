#include<stdio.h>
void g(char** str_ptr) {
    *str_ptr="world";
}
void f() {
    char *str ="hello";
    g(&str);
    printf("%s\n",str);
}
int main() {
  f();
  return 0;
}
