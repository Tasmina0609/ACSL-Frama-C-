/*@ requires n>0;
    requires \valid(t+(0..n-1)) && \valid(s+(0..n-1));

    behavior success:
    assumes \forall integer i; 0<=i<n ==> t[i]==s[i];
    ensures \result == 1;

    behavior failure:
    assumes \exists integer i; 0<=i<n && t[i]!=s[i];
    ensures \result == 0;
*/

int compare(int t[],int s[],int n) {
/*@ loop invariant 0<=i<=n;
    loop invariant \forall integer j;  0<=j<i ==> t[j]==s[j];
    loop variant n-i;
*/
      for(int i=0;i<n;i++) {
            if(t[i]!=s[i]) return 0;
      }
      return 1;
}