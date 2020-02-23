/** Compute the minimum between two integers **/

/*@ 
      ensures \result<=a && \result<=b;
      ensures \result==a || \result==b;
*/

int min(int a,int b) {
      return(a<b) ? a : b;
}