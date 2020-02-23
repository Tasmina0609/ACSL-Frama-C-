/*@ requires \valid(a) && \valid(b);
    requires -1000<*a < 1000;
    requires -1000<*b < 1000;

    assigns *a;
    assigns *b;
    
    ensures *a==\old(*b);
    ensures *b==\old(*a);

    
*/
void swap(int *a,int *b) {
      *a=*a+*b;
      *b=*a-*b;
      *a=*a-*b;
}