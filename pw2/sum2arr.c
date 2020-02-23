/*@ requires size>0;
    requires \valid(t+(0..size-1));
    requires \valid(s+(0..size-1));
    requires \valid(r+(0..size-1));

    requires \forall int i; 0 <= i < size ==> -10000 <= t[i] <= 10000;
    requires \forall int i; 0 <= i < size ==> -10000 <= s[i] <= 10000;
    assigns r[0..size-1];
    ensures \forall integer i; 0<=i<size ==> r[i]==t[i]+s[i];


*/

void sum(int t[],int s[], int r[], int size) {
/*@ loop invariant 0<=i<=size;
    loop invariant \forall integer j; 0<=j<i ==> r[j]==t[j]+s[j];
    loop variant size-i;
*/
      for(int i=0;i<size;i++) {
            r[i]=t[i]+s[i];
      }
 }