function double(n) {
  return n * 2;
}
console.log(double(4));
console.log(double(double(4)));

console.log([1,2,3].map(double));

function sum(l) {
  if (l.length === 0) {
    return 0;
  } else {
    const x = l.pop();
    const l1 = l; // Because pop changes l
    return x + sum(l1);
  }
}
console.log(sum([1,2,3]));
console.log(sum([1,2,3,4]));

function f1(l) {
  return sum(l.map(double));
}
function f2(l) {
  return double(sum(l));
}
console.log(f1([1,2,3]));
console.log(f2([1,2,3]));
