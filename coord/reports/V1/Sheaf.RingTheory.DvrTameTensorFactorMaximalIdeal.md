## What changed

Replaced the sorry in `RingTheory.dvr_tame_tensor_factor_map_maximalIdeal` by a
compiling proof, preserving its signature and public imports. Added proof-only
imports of Mathlib's finite separable normalization theorem, GoingUp, and the new
`Sheaf.RingTheory.DvrTameTensorFactorRamificationBound` module.

The proof constructs the composite scalar tower, proves finiteness of
`integralClosure B E` using `IsIntegralClosure.finite`, proves the tensor quotient
map `alpha : A →+* F` injective, specializes the quantitative bound to `r = n`,
uses `Ideal.ramificationIdx_pos` to force index one, and converts the length-one
quotient to the unique maximal ideal of the localization. Tensor balancing and
`Ideal.eq_bot_of_comap_eq_bot` discharge the injection step without any new hole.
The original node's proof and dependencies now describe these Lean steps.

## Proved and sorry left

Hole closed: `RingTheory.dvr_tame_tensor_factor_map_maximalIdeal`
(node `lem-sbc-dvr-tame-tensor-factor-maximal-ideal`). There is no sorry left in
the item's module.

Hole added: `RingTheory.dvr_tame_tensor_factor_ramificationIdx_le`
(node `lem-sbc-dvr-tame-tensor-factor-ramification-bound`), in the new module
`Sheaf.RingTheory.DvrTameTensorFactorRamificationBound`. Its proof is exactly
`by sorry`; its docstring and node give the auxiliary-root proof with sources.
This is a decomposition, one hole closed and one added, not a claim that the
transitive tame ramification argument has been proved.

The remaining theorem is a quantitative step with an independent exponent `r`:
it bounds the index by `r / gcd(r,n)` even when the tame index does not divide
`n`, and it assumes the finiteness of C and injectivity of alpha that the item's
proof actually establishes. It neither asserts maximal ideal equality nor
repackages that conclusion under the original hypotheses. The proof that uses
it performs the normalization finiteness argument, the kernel argument, the
arithmetic specialization, positivity, and the length/simple-module criterion.

Both modules compile together through lcompile.py. The original statement and
visibility remain identical. No definition, axiom, target, or other held module
was changed. The new statement was checked on `r=1`, `n=1`, `r=n`, and the tame
root examples `n=4, r=6` and `n=2, r=3`: the bounds are respectively 1, r, 1,
3, and 3. Positivity assumptions exclude zero exponents; the finite maximal
tensor quotient is nonzero; Q cannot be zero since it lies over the nonzero
maximal ideal of a DVR. The source argument works for arbitrary base index n;
only r must be a unit. The quantitative bound remains unproved in Lean.

## No longer needed

None. All original statement imports remain necessary for the unchanged
interface. The original normalization finiteness dependency remains used through
Mathlib's `IsIntegralClosure.finite`. No existing node or module is pruned.
The stronger formal-unramifiedness and residue-separability modules are not
imported; they are downstream users, not dependencies of this proof.

## Where the brief, the DAG or earlier work was wrong

The original DAG's step applying 0BRM had no Lean declaration or proof dependency
for the tame calculation. That step could not be applied as a stated Lean lemma.
It is now isolated as the numerical ramification bound. The remaining pieces
of the plan that were called elementary are realized explicitly, including
injectivity of the tensor quotient map. Mathlib's index is defined by quotient
length and converted from ENat, so index positivity is used before interpreting
index one as maximal ideal equality. No mathematical statement is disputed.

LeanSearch returned Internal Server Error; that search is recorded as unavailable.
Lean Finder and local source searches found tower and positivity APIs but no
Abhyankar tensor-factor bound. Searches of the imported blueprint for Abhyankar
and ramification bounds found no duplicate. The trait unit route is retained:
finite normalization, tame DVR base change, and the index-one consequence.

## New nodes

`lem-sbc-dvr-tame-tensor-factor-ramification-bound` records the new quantitative
bound, with the signature verbatim and the same chapter and unit as the item.
Its proof uses an auxiliary root extension of index `r/gcd(r,n)`, whose index over
B is `lcm(r,n)`, applies 0BRM there, and descends the numerical bound by tower
multiplicativity. The existing proved uniformizer-root algebra and the Mathlib
finite separable normalization node are recorded as dependencies. Tags 0BRM,
09EV, 09EM, 09E7 and 032L were read from the Stacks website. No change record is
needed: only proofs and proof imports of the existing module changed.

## Second reading by V1

1. Compared the delivered original module with the repository using diff and
   checked its full theorem signature byte for byte. Verdict: unchanged; only
   the proof and three plain proof imports differ. The original node changes
   only proof, proof_deps and proof_origin. No target, definition or existing
   public import changes, and no change record is required.
2. Compiled both modules in import order with lcompile.py. Compiled scratch
   copies with #print axioms for both declarations: each reports precisely
   propext, Classical.choice, Quot.sound and sorryAx. The sole sorry is the
   named numerical-bound theorem, exactly by sorry. No forbidden declaration
   mechanism, definition, arbitrary chosen data or additional hole occurs.
   Verdict: the reduction is kernel checked, conditional on the listed hole;
   this is a decomposition, not a sorry-free proof or a net hole reduction.
3. Read the numerical-bound statement, docstring, node and sources 0BRM, 09EV,
   09EM and 09E7 against one another. Checked r=1, n=1, r=n and the root
   examples (r,n)=(6,4),(3,2): t is positive, divides r, and n*t=lcm(r,n).
   The unit condition excludes inseparable residue degree greater than one.
   The general bound permits wild base index n, since only the tame exponent
   r and its divisor t must be units. The injective map alpha supplies the
   faithful embeddings needed for the field and normalization identifications.
   Verdict: true, with a complete auxiliary-root argument; this numerical step
   omits the finiteness, injection, positivity and quotient-length work that
   the original proof now performs. It is not a renamed maximal-ideal equality.
   Independent Loogle search for Ideal.ramificationIdx bounds found only tower
   inequalities; Lean Finder search for ramification of composita found tower
   and Galois formulas. Local searches for tame, Abhyankar and ramification/gcd
   found no proved replacement. The downstream unramified theorem depends on
   this item and cannot be used circularly. Closing the numerical hole requires
   formalizing the remaining tame calculation, not a short API application.
4. Read the proof from the conclusion back to its dependencies. The finite
   normalization theorem and integral-kernel lemma are direct Mathlib uses;
   index one is converted through quotient length without a new hole. The new
   module retains its root-algebra and finite-normalization imports as the
   stated proof plan of its open theorem. All original public imports support
   the unchanged signature. The only old proof dependency was finite separable
   normalization, and it is still used, so No longer needed: none is complete.
   Read sk-prop-input-spreading.json and its trait step: the tame-root route
   stays intact. Its existing realized arrays are empty; this delivery neither
   changes them nor claims to complete the whole unit. Verdict: no pruning or
   departure from the unit route.
5. Checked the existing node's four proof steps against the Lean proof, the
   new node's signature against its module, the union of each node's uses
   against proof_deps, and the new node's source, searches, created, blueprint,
   chapter, unit and lean fields. Verdict: coherent. The root algebra is proved
   upstream; the finite-normalization dependency is matched to Mathlib.

Changed only the new theorem's natural-language proof and its matching node
steps: made Frac(S)=F explicit by clearing denominators, explained why the
auxiliary root ring is the normalization of B in K', and explained why the
prime above Q contracts to the unique maximal ideal of A'. These details
justify both local DVR towers used for multiplicativity. No signature or
Lean proof changed. Both declarations' scratch axiom checks passed.

Source pages checked: https://stacks.math.columbia.edu/tag/0BRM,
https://stacks.math.columbia.edu/tag/09EV,
https://stacks.math.columbia.edu/tag/09EM and
https://stacks.math.columbia.edu/tag/09E7.
