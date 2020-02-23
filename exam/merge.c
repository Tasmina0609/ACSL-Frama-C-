/*@ 
    ensures \result>=a && \result>=b && \result>=c;
    ensures \result==a || \result==b || \result==c;
    ensures a>=b && a>=c ==> \result==a;
    ensures b>=a && b>=c ==> \result==b;
    ensures c>=a && c>=b ==> \result==c;
*/

int max3(int a,int b,int c) {
      int max;
      if((a >= b) && (a >= c)) {
        max = a;
      }
      else if((b >= a) && (b >= c)) {
        max = b;
      }
      else if((c >= a) && (c >= b)) {
        max = c;
      }
    return max;
}

/*@ requires 1000>size>0;
    requires \valid(t+(0..size-1));
    assigns t[0..size-1];

    ensures \forall integer i; 0<=i<size ==> t[i] == (i*2) ;
    ensures \forall integer i; 0<=i<size-1 ==> t[i]<=t[i+1];  
*/
 
void doubleint(int t[],int size) {  // void double() --> not possible since datatype!
/*@ loop invariant 0<=i<=size; 
    loop invariant \forall integer j; 0<=j<i ==> t[j] == (j*2) ;
    loop invariant \forall integer j; 0<=j<i-1 ==> t[j]<=t[j+1];
    loop variant size-i;
*/
       for(int i=0;i<size;i++) {
          t[i]=i*2;
       }
}

/*@ requires size>0;
    requires \valid(t+(0..size-1));
    assigns \nothing; 

    behavior success:
      assumes \forall integer i; 0<=i<size-1 ==> t[i]<=t[i+1];
      ensures \result==1;

    behavior failure:
      assumes \exists integer i; 0<=i<size-1 && t[i]>t[i+1];
      ensures \result==0;
*/

int increasing(int t[], int size){
/*@   loop invariant 0<=i<=size-1;
      loop invariant \forall integer j; 0<=j<i ==> t[j]<=t[j+1];
      loop variant size-i;  
*/
      for(int i=0;i<size-1;i++) {
            if( (t[i] > t[i+1]) )  return 0;
      }
      return 1; 
}
