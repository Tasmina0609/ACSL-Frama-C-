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

/*@ requires 1000>taille>0;
    requires \valid(t+(0..taille-1));
    assigns t[0..taille-1];

    ensures \forall integer i; 0<=i<taille ==> t[i] == (i*2) ;
    ensures \forall integer i; 0<=i<taille-1 ==> t[i]<=t[i+1];  
*/
 
void doubleint(int t[],int taille) {  // void double() --> not possible since datatype!
/*@ loop invariant 0<=i<=taille; 
    loop invariant \forall integer j; 0<=j<i ==> t[j] == (j*2) ;
    loop invariant \forall integer j; 0<=j<i-1 ==> t[j]<=t[j+1];
    loop variant taille-i;
*/
       for(int i=0;i<taille;i++) {
          t[i]=i*2;
       }
}

/*@ requires taille>0;
    requires \valid(t+(0..taille-1));
    assigns \nothing; 

    behavior success:
      assumes \forall integer i; 0<=i<taille-1 ==> t[i]<=t[i+1];
      ensures \result==1;

    behavior failure:
      assumes \exists integer i; 0<=i<taille-1 && t[i]>t[i+1];
      ensures \result==0;
*/

int increasing(int t[], int taille){
/*@   loop invariant 0<=i<=taille-1;
      loop invariant \forall integer j; 0<=j<i ==> t[j]<=t[j+1];
      loop variant taille-i;  
*/
      for(int i=0;i<taille-1;i++) {
            if( (t[i] > t[i+1]) )  return 0;
      }
      return 1; 
}


/*@ requires taille>0;
    requires \valid(t+(0..taille-1));
    assigns \nothing; 

    ensures (\forall integer i; 0<=i<taille ==> t[i] > t[i+1]) ==> \result==0;
    ensures (\forall integer i; 0<=i<taille ==> t[i] < t[i+1]) ==> \result==0;
    
*/

int monotonic(int t[], int taille) {
      int inc=1,dec=1;
/*@ loop invariant 0<=i<=taille-1;
    loop invariant (\forall integer j; 0<=j<i-1 ==> t[j] > t[j+1]) ==> inc==0;
    loop invariant (\forall integer j; 0<=j<i-1 ==> t[j] < t[j+1]) ==> dec==0;
    loop variant taille-1-i;
*/
      for(int i=0;i<taille-1;i++) {
            if ( t[i] > t[i+1])  
                 inc=0;
            if ( t[i] < t[i+1]) 
                 dec=0;
      }
      return inc || dec;
}
