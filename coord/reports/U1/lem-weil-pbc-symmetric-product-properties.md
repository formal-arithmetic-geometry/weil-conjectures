## Worker report

The module `Sheaf.AlgebraicGeometry.SymmetricProductProperties` states
`AlgebraicGeometry.symmetricProduct_properties` with a single `sorry` proof. No theorem
is proved. The companion definition module is fully implemented, with no new postponed
proofs or hollow data. The item's statement is unchanged.

Hypotheses and objects:

- An arbitrary scheme S is `(S : Scheme.{v})`, with its universe explicitly bound.
- The positive integer n is `m + 1`, `(m : ℕ)`. This parametrizes every n ≥ 1;
  `Nat.zero_lt_succ m` supplies the positivity argument of the recorded polynomial.
- P^1_S and P^n_S are the recorded `ProjectiveSpace`, with homogeneous coordinate
  types `ULift (Fin 2)` and `ULift (Fin (m + 2))`. ULift changes no coordinate set.
- The n-fold fibre product and its projections are a product cone in `Over S`:
  `X : Over S`, `pr : Fin (m + 1) → (X ⟶ Over.mk (ℙ(ULift (Fin 2); S) ↘ S))`,
  and `IsLimit (Fan.mk X pr)`. These are the node's product universal property,
  not a restriction to a special product. The inductive fibre product in the node
  is one such cone. Conversely the cone is uniquely isomorphic to that inductive
  product, preserving all projections. `X.hom` is p_n; the Over morphisms encode
  every equality pr_i followed by q_1 = p_n. Any test scheme with maps having a
  common composite to S becomes an Over object, so the stated universal property
  is exactly the node's tuple characterization. This avoids making another chosen
  product definition.
- O(1) is the recorded `ProjectiveSpace.twist _ S 1`. Its source definition pulls
  the integral Proj twist along `toProjInt`, exactly the second projection specified
  in the node. `twistOneSection` is the recorded pulled-back integral coordinate.
- `symmetricProductFactor` is tensorPullback pr_i applied to this twist;
  `symmetricProductFactorSection pr i 0/1` are x_i/y_i. Section pullback uses the
  unit of `Classical.choose (exists_tensorPullbackAdjunction (pr i))`.
- `symmetricProductLineBundle` is the existing positiveTensorFamily of the factors,
  with left-associated parentheses. Its coefficient sections are defined by the
  existing positiveTensorFamilySection and the subset sum. Top-open values and
  compatible families are identified through `homOfGlobalSection` and unitHomEquiv.

Clauses:

- (a) The first conjunct equates the recorded `symmetricProductPolynomial` with
  the sum over `Finset.univ.powerset.filter (fun J ↦ J.card = j.val)` of the two
  variable products, over J and its complement. The next conjunct says every
  supported monomial d satisfies `d (Sum.inl i) + d (Sum.inr i) = 1` for each pair i:
  precisely multihomogeneity of degree (1,...,1). The meaning as a global section
  is implemented in `symmetricProductCoordinateSection`: sum of the ordered tensors
  selecting x_i inside J and y_i outside J. It sums the corresponding unit-to-L_n
  morphisms, then applies unitHomEquiv, so this is the ordinary additive sum of
  global sections, not an evaluation of a nonhomogeneous polynomial in one module.
- (b) `∀ z : X.left, ∃ j, z ∈ nonvanishingLocus L_n ((F_j).val (op ⊤))` says some
  residue-field fibre value is nonzero at each point. The recorded nonvanishingLocus
  means the germ is outside the maximal ideal times its stalk. The existential
  `hL : L_n.IsInvertible` and `hs : Epi (L_n.freeHomEquiv.symm F)` also state
  invertibility and generation; neither is assumed as an extra hypothesis.
- (c) An existential σ is equated with the recorded homOfGeneratingSections applied
  to p_n, L_n and F, using the concluded hL and hs. Its first projection is X.hom.
  The second is ψ followed by the integral model's toProjInt. The existential
  section-preserving isomorphism identifies ψ^* O(1) with L_n and each ψ^* T_j
  with F_j. This is the node's coordinate formula [F_0:...:F_n]. As in the recorded
  functor-of-points module, ψ lands first in projective space over Spec ℤ; its
  second projection canonically identifies that scheme with the raw integral Proj.
  Consequently the projection clause has the same raw integral target as the node.
- (d) For every `π : Equiv.Perm (Fin (m + 1))` there is `τ : X ≅ X` in Over S.
  Its hom and inv have respectively the projections pr_(π i) and pr_(π.symm i).
  Thus it is precisely τ_π and its inverse τ_(π⁻¹), and is automatically over S.
  The isomorphism β from tensorPullback τ.hom.left of L_n to L_n carries every
  pulled-back coefficient section to itself. Finally `τ.hom.left ≫ σ = σ` is
  exactly σ_n ∘ τ_π = σ_n (Lean composition is written left to right).

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: ProjectiveSpace, its over
  instance (first pullback projection), and ProjectiveSpace.toProjInt (second).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: pullback, fst, snd
  and the universal lift; the finite product cone expresses their iterated universal
  property through `Fan.mk` and `IsLimit` from Mathlib's Products module.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: ProjectiveSpace.twist
  and twistOneSection; their full definitions identify the integral-model pullbacks.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: Scheme.Modules.IsInvertible.
- `Sheaf.AlgebraicGeometry.SymmetricProductPolynomial`: symmetricProductPolynomial.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints`:
  projectiveSpace_functor_of_points, imported through the morphism-by-sections module;
  its universal generating pair and section-preserving isomorphism give the ψ clause.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`:
  ProjectiveSpace.homOfGeneratingSections; its definition pairs the structural map
  with integralHomOfGeneratingSections followed by the integral model's toProjInt.
- `Sheaf.AlgebraicGeometry.PositiveTensorFamily`: Scheme.Modules.positiveTensorFamily
  and positiveTensorFamilySection. These existing definitions were reused, not copied.
- `Sheaf.AlgebraicGeometry.TensorPullback` and TensorPullbackAdjunction:
  Scheme.Modules.tensorPullback and exists_tensorPullbackAdjunction.
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`:
  Scheme.Modules.homOfGlobalSection; Mathlib SheafOfModules.unitHomEquiv identifies
  the top-open section with its compatible restrictions.
- `Sheaf.AlgebraicGeometry.Ample`: Scheme.Modules.nonvanishingLocus; the imported
  InvertibleGeneratingSectionsFibre module states its equivalence with generation.

Edge cases checked: m=0 (n=1) gives L_1 as its single factor, F_0=y_1 and F_1=x_1;
there is only the identity permutation. For all n, j=0 and j=n use the unique empty
and full subsets. n=0 is outside this node and not silently included. The empty base
and empty product have vacuous pointwise generation but still the unique morphisms
and isomorphisms asserted. No reducedness, characteristic or Noetherian hypotheses
are imposed; the fibre proof works over every residue field. Universes are explicit,
and the integer coefficient ring and coordinate sets are lifted to the scheme universe.

Searches: msearch LeanFinder for the full symmetric-product properties returned only
Weierstrass projective-coordinate lemmas; Loogle for ProjectiveSpace and Polynomial.coeff
reported unknown ProjectiveSpace (absent from Mathlib). msearch grep for
`symmetricProduct|SymmetricProduct` in AlgebraicGeometry found no matches. Local rg
of WeilConjectures found no symmetric-product declaration or blueprint-id reference;
rg of lean/Sheaf found only symmetricProductPolynomial. For the tensor sections,
LeanSearch was unavailable (Internal Server Error); LeanFinder returned Picard-group,
binary presheaf tensor and unrelated results. Local DAG searches found the already
landed def-sc-positive-tensor-family, whose declarations are reused. Blueprint search
for symmetric product found the merged lemma-weil-pbc-symmetric-product-p1, not a
section definition. The new node contains the actual msearch result records and the
local-search results. No exact existing theorem was found.

The literature tree is not present in this read-only clone. I read the full node proof,
all recorded dependency modules, and the primary Stacks pages
https://stacks.math.columbia.edu/tag/0A4F and https://stacks.math.columbia.edu/tag/01NE.
0A4F confirms the coordinate product formula with reverse indexing; the delivery keeps
the blueprint's coefficient-of-t^j indexing, as the polynomial dependency requires.
No statement dispute, correction or unusable dependency was found.

Both modules compiled together on the server without errors or warnings; the combined
file was 182 lines and compiled in 4.0 seconds. The definition module also compiled
separately. Different explicit universe names in sibling modules avoid a duplicate
universe declaration when scompile concatenates their bodies.

## New nodes

`def-weil-pbc-symmetric-product-sections` defines the pulled-back factor modules and
coordinate sections, their ordered line bundle L_n, and the sum-of-pure-tensors sections
F_j used in the item's sections paragraph and (a). Its source is that paragraph and
Stacks Tag 0A4F's formula. The polynomial dependency supplies only integer polynomials,
not sections of different factor modules. Mathlib and source searches found no exact
construction. The existing def-sc-positive-tensor-family supplies the generic ordered
tensor product and section tensor and is explicitly cited and imported. The new node
therefore adds only the symmetric-product specialization, not a second tensor API.

## Second reading by U1

I independently read the repository node, its six proof steps, the two delivered
modules and the new definition node. The original statement is unchanged and there
is no statement_change to audit. Verdict: the Lean states the node, with no added
mathematical hypothesis, omitted conclusion or private replacement dependency.
No Lean or node repair was needed; this reading adds this report section only.

Objects, hypotheses and clauses, in the order of the node:

1. Arbitrary scheme S: `(S : Scheme.{v})`. Positive n: `(m : ℕ)` and
   `Fin (m + 1)`, with `Nat.zero_lt_succ m` for the polynomial. This covers
   every positive n, including n=1. Verdict: exact.
2. P^1_S and P^n_S: `ℙ(ULift.{v} (Fin 2); S)` and
   `ℙ(ULift.{v} (Fin (m + 2)); S)`. I opened the recorded ProjectiveSpace
   declaration, its over instance and toProjInt: the definition is the
   pullback over Spec (ULift ℤ), the structural map is fst, and toProjInt
   is snd to the integral Proj. ULift preserves the finite coordinate sets.
   Verdict: exact, with no dimension or base-ring specialization.
3. The n-fold fibre product and its projections: `(X : Over S)`, `pr`,
   and `_hprod : IsLimit (Fan.mk X pr)`. An Over morphism includes the
   compatibility with the common structural map `X.hom`. An iterated
   pullback of the recorded fibre-product dependency is such a product
   cone; conversely the universal properties give a unique isomorphism
   respecting each projection. Hence the apparently more general cone
   introduces no stronger assertion about the mathematical object. Every
   test scheme with a common composite to S is an object of Over S.
   Verdict: exactly the tuple universal property and p_n in the node.
4. O(1), T_0,T_1, their pullbacks, and L_n: the delivered definitions use
   the recorded `ProjectiveSpace.twist _ S 1` and `twistOneSection`,
   `Scheme.Modules.tensorPullback`, and the unit of the chosen
   `exists_tensorPullbackAdjunction`. The adjunction's sectionwise unit
   is explicitly pinned in its source theorem, so an arbitrary adjunction
   cannot rescale these sections. `homOfGlobalSection` restricts its
   top-open input to a compatible section family; `unitHomEquiv` returns
   that family. `positiveTensorFamily m` and its Section declaration
   are the existing ordered, left-associated tensor recursion, including
   the single-factor base case. Verdict: exactly x_i, y_i and L_n.
5. (a), polynomial identity: the first conjunct uses the recorded
   `symmetricProductPolynomial` (which I opened: coefficient j of the
   product of C(x_i)*t+C(y_i)), summed over subsets with card=j, and
   products of inl variables on J and inr variables on its complement.
   The second conjunct says every supported monomial has exponent sum
   one in each pair: exactly multidegree (1,...,1). No nonzero condition
   on the polynomial is added. `symmetricProductCoordinateSection`
   defines the section sum of the ordered tensors, selecting coordinate
   0 inside J and coordinate 1 outside J. Transporting each tensor to
   a unit-to-L_n morphism, adding, and applying unitHomEquiv is the
   ordinary sum of these sections. Verdict: all of (a), including its
   meaning as a section, is present.
6. (b): `∀ z : X.left, ∃ j, z ∈ nonvanishingLocus ...` asserts that
   some F_j has a germ outside the maximal ideal times the stalk. I
   opened nonvanishingLocus: this is exactly nonzero residue-field fibre
   value, not nonzero germ alone. The existential hL asserts invertibility
   and hs asserts `Epi (L.freeHomEquiv.symm F)`, generation by the same
   sections. They are conclusions, not hypotheses. Verdict: exact.
7. (c): the existential σ is required equal to the recorded
   `ProjectiveSpace.homOfGeneratingSections` with p_n=X.hom, L_n and F.
   Its first projection equals X.hom. The existential ψ has the same
   second projection after `toProjInt`, and e identifies its tensor
   pullback of the universal twist with L_n while carrying every
   pulled-back coordinate to F_j. I opened both integralHomOfGeneratingSections
   and homOfGeneratingSections: the latter is the pullback pairing
   with the selected classifying integral morphism. The integral base
   model ℙ(I;Spec ℤ) canonically projects isomorphically to raw Proj,
   so the second-projection equation is the node's equation. The
   section-preserving e is precisely the coordinate formula, not merely
   an unlabelled line-bundle isomorphism. Verdict: exact.
8. (d): for every `Equiv.Perm (Fin (m + 1))`, `τ : X ≅ X` in Over S
   has `τ.hom ≫ pr i = pr (π i)` and the inverse equation with π.symm.
   These equations characterize the permutation and its inverse. β
   identifies tensorPullback τ.hom.left of L_n with L_n and carries each
   pulled-back F_j to F_j. Finally `τ.hom.left ≫ σ = σ` is σ_n∘τ_π=σ_n.
   It uses the same σ, and the same sections, as (b) and (c). Verdict: exact.

Source audit: the literature tree is unavailable in this clone, so I fetched
the primary Stacks .tex files into the sandbox scratchpad and read
etale-cohomology.tex, proof of lemma-reduce-to-P1 (Tag 0A4F), especially
lines 18587–18603, and constructions.tex, lemma-projective-space (01NE),
definition-projective-space and its following paragraph (01NF), and
lemma-standard-covering-projective-space (01NG), lines 2775–2886. The
symmetric-product paragraph applies for every scheme S and n≥1; the preceding
affine reduction in the proof does not restrict this construction. Stacks'
descending coefficient order differs from the blueprint's documented ascending
order; the delivered polynomial and tensor section both follow the blueprint.
Primary pages also checked: https://stacks.math.columbia.edu/tag/0A4F,
https://stacks.math.columbia.edu/tag/01NE, and
https://stacks.math.columbia.edu/tag/01NG.

Edge cases: m=0 gives one factor, F_0=y_0 and F_1=x_0 and only the identity
permutation. At j=0 and j=n the empty and full subsets each contribute the
correct pure tensor; empty products of polynomial factors are 1. n=0 is
explicitly outside the node. Empty schemes impose no missing Nonempty
hypothesis: the pointwise condition is vacuous and module generation,
classification and permutations still make sense. The zero module on an
empty scheme is covered by invertibility there; no zero module is assumed
on a nonempty scheme. All characteristics and nonreduced bases are allowed.
Scheme universe v is arbitrary; coordinate sets and integral coefficients
are lifted to it, and there is no independent smaller test-object universe.

Independent searches used different terms from the worker: msearch LeanFinder
`tensor product coordinate sections product projective lines permutation
invariance` returned Projectivization.cross, Picard tensor identities and
SymmetricPower.Rel.perm, none a scheme theorem or this tensor-section
construction. msearch Loogle `MvPolynomial.IsWeightedHomogeneous` returned
the existing generic weighted-degree predicate and its algebraic lemmas;
the supported-exponent clause is its direct multidegree meaning, and no
symmetric-product scheme statement was found. Local rg for
`symmetric.?product|projective.?line.*product|coefficient.*section|tensor.*coordinate`
in Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf found only
comments in ProjectiveLine and ProjectiveSpaceBaseChangeReduction, generic
twist section constructions, and the existing symmetricProductPolynomial.
I opened the polynomial declaration; it supplies no tensor sections. DAG
search and blueprint_refs.py search `symmetric product` found the merged
blueprint ancestor and the coefficient node, not another section definition.
The worker's LeanSearch failure remains recorded in the new node.

New-node reading (H12): def-weil-pbc-symmetric-product-sections introduces
only the specialization from the source's sections paragraph and (a), for
any maps X→P^1_S; it does not duplicate the generic positive tensor API.
Its factor definitions additionally allow n=0 with no index i, harmless
since the line bundle and coefficients require m+1 factors. All cited
notions have recorded dependencies, which I read against their declarations.
The node has the prescribed definition/split status, empty proof fields,
source, searches, creation and blueprint ancestry, audit-none fields,
chapter/unit and Lean record; the item cites it. No dependency module is
delivered and no unusable dependency was found (H13).

H5–H9: the new definitions contain explicit data and no sorry. The sole
new theorem has the required sorry proof, with the node's six proof steps
in its docstring and the correct blueprint id. Every new declaration has
a source docstring. No local notation, local instance, private definition,
let/show binder or additional theorem was introduced. Universes and variables
are bound; module paths, namespaces, imports and line lengths follow the
contract. Both modules compiled together on the server in 5.4 seconds with
no errors or warnings. The normalized node signatures match the file signatures.
