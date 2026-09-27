# Fewer than 3.178^n stable matchings

English proof and formal verification note

25 September 2026 · smp-max

Companion text guide. The paper PDF is typeset directly from `PROOF.tex`.

## 1. The theorem and its scope

For a strict, complete stable-marriage profile I with n men and n women,
write stableCount(I) for the number of all stable perfect matchings.
The complete Lean development proves the following statement.

```math
n > 0  implies  stableCount(I) < (1589/500)^n = 3.178^n.
```

Taking the maximum over profiles gives f(n) < 3.178^n for every positive
integer n. The statement has no restriction on preference patterns,
rotation sizes, or the size of n. The condition n > 0 is explicit:
the strict inequality would fail at n = 0, where there is one empty matching.

The formal theorem is `SmpMax.General.stableCount_lt_3178_pow` in
`lean/SmpMax/General/JointEntropyUpperBound.lean`. Its exact signature is:

```lean
theorem stableCount_lt_3178_pow {n : ℕ}
    (hn : 0 < n) (I : Profile n) :
    (stableCount I : ℝ) < (1589 / 500 : ℝ) ^ n
```

The rational 1589/500 is exactly 3.178. No floating-point representation
is used in this statement or in its numerical proof. This note explains
the argument and points to its formal components; the complete machine
proof is the accompanying Lean source. Optimality and priority are not
claims of this review package.

## 2. Definitions and the finite revelation inequality

The file `Definitions.lean` represents a preference row by a permutation
of ranks 0,...,n-1. Lower ranks mean better partners. A profile contains
one such row for each man and each woman. A matching is a bijection from
men to women, with an inverse giving each woman's partner.

A pair (m,w) blocks a matching if both participants strictly prefer each
other to their assigned partners. `Stable` excludes every blocking pair.
`stableCount` is the cardinality of the finite set of all bijections
satisfying that predicate. A stable pair is any pair appearing in at
least one stable matching. These definitions do not encode the theorem
as a hypothesis or restrict the family being counted.

Let S be the stable matching family. If S is empty the result is immediate.
Otherwise choose a reference matching μ uniformly from S. Fix a reveal
order, and expose the men's partners one coordinate at a time. For the
next man m, let X_m be the number of partners occurring among stable
matchings that agree with μ at every already exposed coordinate.

The chain rule for finite entropy and the entropy bound by logarithmic
support size give:

```math
log |S| ≤ E_μ Σ_m log X_m(μ,π).
```

The formal development proves the finite counting version, including the
zero-count case, before averaging over reveal orders. The average may use
any fixed finite sample of injective rank assignments. Consequently:

```math
log |S| ≤ E_(μ,π) Σ_m log X_m(μ,π).
```

Only the n actual men's coordinates contribute to this sum. The later
auxiliary labels alter reveal ranks, never the matching instance or its
number of coordinates. The proof uses a sample space fixed independently
of μ. See `MatchingRevelation.lean` and `ExtendedRevelation.lean`.

## 3. A common padded gap

Fix μ and a man m. Order all stable partners of m from best to worst,
and label each partner w by her owner μ⁻¹(w). These labels are distinct
because μ is a bijection. The reference partner μ(m) is the pivot, labeled m.

Stable-pair opposition supplies the basic barriers: a revealed owner
on either side rules out compatible partners farther beyond that owner.
This follows from the original stability inequalities on both sides of
the market. It uses the full stable-partner family, not a sampled subfamily.

Pad this list by 24 auxiliary labels at each end. Use a uniformly random
permutation π of the n real labels and these 48 auxiliary labels. The same
48 labels and the same π are used for every man. Each man's padded list
has distinct labels; independence between different men's costs is unnecessary.

Let L and R be the lengths of consecutive later-revealed positions on the
left and right of the pivot, stopping at an earlier label or the padded
end. Set K = 1 + L + R. The original support barriers imply that every
compatible stable partner lies in this common gap. A finite permutation
count and telescoping logarithmic sum give a uniform bound on E_π log K.

For a positive cutoff N, define:

```math
B_N = Σ_(k=2,...,N) [2/(k+1)] log(k/(k-1))
      + 1/(2N) + 3/(2(N+1)).

E_π log K ≤ B_N.
```

This is `refinedLogBound N` in Lean. The tail estimate is finite and
uniform in the length of the partner list. No equality to an infinite
series is needed for the theorem. At cutoff 512, the exact rational
certificate establishes:

```math
B_512 < log(1665987/500000) = log(3.331974).
```

The relevant files are `PartnerIntervals.lean`, `PermutationCounting.lean`,
`LogTail.lean`, `RefinedLogBound.lean`, `RefinedLogCertificate.lean`, and
the longer padded-list interfaces `LongPaddedOwners.lean` and
`LongPaddedSupport.lean`.

## 4. Propagation and directional exclusions

Fix one direction in a man's stable-partner list. Define g(m) to be the
reference owner of the nearest stable partner in that direction; put
g(m) = m when there is no partner in that direction.

If m crosses a worse stable partner w in a compatible stable matching,
then her reference owner must become worse off. A worsening change
propagates again to that owner's nearest worse-partner owner. The
corresponding statement toward better partners also holds, proved using
stable-pair opposition in the original profile.

Thus crossing a partner owned by a forces g(a) to change in that direction.
If g(a) has already been revealed, agreement with μ is contradicted.
That partner and every farther partner are excluded. These are the
successor and predecessor barriers in `SuccessorPropagation.lean` and
`BidirectionalPropagation.lean`. The argument does not reverse preferences.

Let l and r be the actual left and right compatible-support caps, centered
at the reference partner. They satisfy l ≤ L and r ≤ R. The reference
matching itself is compatible, so X_m is positive, and:

```math
1 ≤ X_m ≤ T,                 T = 1 + l + r.
D_L = log K - log(1+l+R).
D_R = log K - log(1+L+r).
```

Both directional losses are nonnegative and measured against the same
random gap K. The support need not occupy every position between its
extremes; its cardinality is bounded by that interval length. Formal support
caps and their propagated bounds are in `SupportCaps.lean` and `PartnerFrame.lean`.

## 5. Directional events and their exact savings

Write a_j = log((j+2)/(j+1)). The basic directional saving is the rational
number δ = 467/20000. The joint argument also uses ε = 307/500000.

### Short sides and noncycles

If a side has at most one real stable partner, its actual cap is at most
one. Five padded-gap event contributions, with nested contributions
telescoped before averaging, give:

```math
α = a_1/12 + a_2/10 + a_3/15 ≥ 3(δ+ε).
```

If g(g(m)) differs from m, the first partner has a propagation witness
outside the pivot and first neighbor. Three disjoint events, corresponding
to opposite gap lengths 0, 1, and 2, give at least:

```math
β = a_0/12 + a_1/30 + a_2/60 ≥ 3(δ+ε).
```

Witness coincidences with the first three opposite labels are covered
separately. They give the same certified lower bound or a larger one.
The short-side and first-step estimates are proved by
`LongDirectionalSaving.lean`, `JointDirectionalSaving.lean`, and their
logarithm certificates.

### Regular second-step events

Suppose there are at least two stable partners on the chosen side,
g(g(m)) = m, and let b own the second partner. In the regular case,
u = g(b) differs from the pivot, first neighbor, and second neighbor.
Revealing u forces the chosen-side cap to be at most one.

For j = 0,...,23, require u and opposite-side label j+1 before the pivot,
and the first j opposite labels and first two chosen-side labels after it.
The opposite gap length is exactly j and the chosen gap length is at
least two. The resulting loss is at least a_(j+1). Different j give
disjoint events.

If u is outside the 24 opposite labels, the exact probability is:

```math
p_j = 2/((j+5)(j+4)(j+3)).
```

If u equals opposite label i+1, for i = 0,...,23, the probabilities are:

```math
p_(i,j) = 2/((j+5)(j+4)(j+3))   when j < i;
          1/((j+4)(j+3))         when j = i;
          0                     when j > i.
```

These are finite relative-order counts. For p specified distinct labels
before the pivot and q specified distinct labels after it, the probability
is p! q!/(p+q+1)!. There is no assumption of probabilistic independence
between labels. All 25 possible witness rows satisfy:

```math
Σ_(j=0,...,23) p_(i,j) a_(j+1) ≥ δ = 467/20000.
```

Here the outside row is treated as i = 24. `LongEventRows.lean` proves
that every eligible witness falls into one of these rows, and
`LongerLogCertificate.lean` checks all weighted lower bounds exactly.

## 6. The simultaneous-cap remainder

The product identity for the two losses is:

```math
(1+l+R)(1+L+r) - K T = (L-l)(R-r) ≥ 0.
```

Retain its full logarithmic remainder rather than just its sign:

```math
J = log((1+l+R)(1+L+r)/(K T))
  = log(1 + (L-l)(R-r)/(K T)) ≥ 0.

log X_m ≤ log K - D_L - D_R - J.
```

When L,R ≥ 2 and l,r ≤ 1, we have T ≤ 3 and
5(L-1)(R-1) ≥ 1+L+R. Therefore J ≥ log(16/15).
The estimate is attained in this local algebraic bound at L=R=2, l=r=1.
See `JointGapSaving.lean`.

For regular second-step witnesses on both sides, require the witnesses
before the pivot and the four nearest side labels after it. Distinct
witnesses avoiding those four labels give probability 2!4!/7! = 1/105.
Coincident witnesses give probability 1!4!/6! = 1/30. Thus in the
collision-free case the joint expected saving is at least ε, since:

```math
log(16/15)/105 ≥ ε = 307/500000.
```

A witness can instead coincide with one of the first two opposite labels.
That prevents the proposed joint event, but increases its own directional
saving. The two relevant lower bounds are a_1/12 and a_1/30 + a_2/20;
both are at least δ+ε. The other direction retains its δ bound.
Consequently the combined saving is at least 2δ+ε in every regular
cross-direction witness configuration. `JointGapGeometry.lean` and
`JointDirectionalSaving.lean` cover these coincidences explicitly.

## 7. Exceptional vertices and global charging

The joint bonus cannot be assigned to every man separately. For each
direction, let B be the noncycle set {m : g(g(m)) differs from m}.
Let D contain the exceptional men with at least two partners on that
side, g(g(m))=m, and g(b) in {m,g(m)}, where b owns the second partner.

Charge such a man m to b. The neighbor-owner activity lemma ensures
g(b) differs from b. The exceptional relations then imply g(g(b)) differs
from b, so b belongs to B. Conversely, a man charging a given b must be
one of g(b) or g(g(b)). Each fiber has at most two elements. Hence:

```math
|D| ≤ 2 |B|.
```

Every directional mean loss is nonnegative. Outside D it is at least δ.
On B it is at least 3(δ+ε), using the short-side estimate when needed.
For a man regular on both sides, Section 6 supplies the joint gain.
If either side is short, its stronger saving already covers that local
combined target. These facts are instantiated for actual matchings in
`JointMatchingSaving.lean`.

Let S_m be the combined expected loss D_L + D_R + J. Write b_L,b_R and
d_L,d_R for the indicators of the two B and D sets. The charging lemma
proves the pointwise accounting inequality:

```math
S_m ≥ 2δ+ε + 2(δ+ε)(b_L+b_R) - (δ+ε)(d_L+d_R).
```

Summing over men and applying |D| ≤ 2|B| separately in each direction
cancels the possible deficits. This yields:

```math
Σ_m S_m ≥ n(2δ+ε).
2δ+ε = 23657/500000 = 0.047314.
```

The finite-map fiber estimate is in `SuccessorCharging.lean`; the
combined weighted argument is `JointCharging.sum_joint_saving_ge`.
This is an aggregate estimate over men and includes the cost of the
exceptional vertices.

## 8. Exact arithmetic and final assembly

The gap estimate, support inequality, and combined charging estimate give,
for every stable reference matching μ:

```math
E_π Σ_m log X_m(μ,π) ≤ n(B_512 - 2δ - ε).
```

Averaging over references and applying the finite revelation inequality
therefore bounds the complete count by:

```math
stableCount(I) ≤ exp(n(B_512 - 2δ - ε)).
```

It remains to compare the exponent with log(1589/500). All event floors
and final logarithmic comparisons use finite positive logarithm series
with rational arguments. For 0 ≤ x < 1, the series for
log((1+x)/(1-x)) supplies lower partial sums and an explicit positive
remainder bound. For a_j the argument is x=1/(2j+3); six positive terms
justify the rational floors used in all 25 event rows.

For the final comparison, use x=76987/3254987. Then:

```math
(1+x)/(1-x) = (1665987/500000)/(1589/500).
```

Four series terms and their rational remainder bound certify that the
logarithm of this ratio is less than 2δ+ε. Together with the earlier
strict bound B_512 < log(1665987/500000), this proves:

```math
B_512 - 2δ - ε < log(1589/500).
```

Since n > 0, multiplication by n preserves strictness and the exponential
function is strictly increasing. The exact final chain is:

```math
stableCount(I)
  ≤ exp(n(B_512 - 2δ - ε))
  < exp(n log(1589/500))
  = (1589/500)^n.
```

`JointLogCertificate.refinedLogBound_sub_savings_lt_log` proves the
numerical inequality. `JointEntropyUpperBound.lean` performs the support
and entropy assembly and proves the public count theorem. Lean's
`norm_num` constructs proofs of rational comparisons; Python is not
an oracle or hypothesis of the theorem.

## 9. Reading and verifying the formal proof

The bundle contains 56 unchanged general proof modules. The target's
transitive local dependency closure has 45 modules. The other modules
retain completed earlier bounds and their checks. `SOURCE_MAP.md` lists
every module, and `source-index.json` records hashes and the target's
dependency order.

Start with `Definitions.lean`, then inspect the statement in
`JointEntropyUpperBound.lean`. The main supporting obligations are:

- Exact conditional supports and the finite revelation count inequality.
- Uniform finite permutation gap bound and rational logarithm certificate.
- Propagation barriers interpreted in the original stable profile.
- All directional event rows, including witness coincidences and list ends.
- Joint loss inequality and simultaneous or colliding witness cases.
- At-most-two exception fibers and the complete combined charging sum.

The entry point `lean/Check3178.lean` pins the theorem with every hypothesis
explicit and prints the definitions and final axiom dependencies.
The retained audit `lean/checks/GeneralEntropy.lean` checks 112 general
statements. The final theorem depends only on `propext`, `Classical.choice`,
and `Quot.sound`. No external SAT certificate or numerical validation
script is needed to justify it.

From the bundle root, run `python3 tools/verify.py --fetch` for the pinned
dependency setup, build, audits, and final-module kernel replay. Then
`python3 tools/verify.py --kernel all` also replays all 45 local target
dependency modules. With dependencies already present, omit `--fetch`.
The package's retained `evidence/verification.json` and logs report the
source build, audits, and replay conducted on 24 September 2026. The
25 September LaTeX edition preserves the checked Lean project and
verification logs byte for byte.
