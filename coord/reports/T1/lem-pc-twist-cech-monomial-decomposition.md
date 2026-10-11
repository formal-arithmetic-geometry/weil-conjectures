## Worker report

The module Sheaf.AlgebraicGeometry.ProjectiveSpace.TwistCechMonomialDecomposition states
`AlgebraicGeometry.ProjectiveSpace.twist_cech_monomial_decomposition`, with `sorry` only.
No definition is introduced and no theorem is proved.

Hypotheses and clauses:
- The arbitrary commutative ring is `(A : Type u) [CommRing A]`; dimension and twist are
  `(n : ℕ) (hn : 1 ≤ n) (d : ℤ)`.
- Projective space and O(d) use `ProjectiveSpace.twist` on projective space over Spec A.
  The coordinate set is `ULift.{u} (Fin (n+1))`, canonically the n+1 coordinates, lifted to
  the ring's universe because the upstream projective-space construction shares their
  universe. This imposes no restriction on A. Stacks 01XS identifies this relative model
  with Proj A[x_0,...,x_n], compatibly with the twists.
- Every nonempty J is `(s : Set (ULift ...)) (hs : s.Nonempty)`. Its open is
  `toProjInt ... ⁻¹ᵁ basicOpenInt ... s`. Upstream
  `preimage_basicOpenInt_range` identifies these with standard intersections.
- `b s hs` is an A-linear equivalence from `laurentExponents s d →₀ A` to sections.
  `MvPolynomial.laurentExponents` means sum e_i=d and e_i≥0 outside s.
  The first conjunct specifies `b` on every `Finsupp.single e a` as the coefficient a
  times the actual `twistMonomialSection`. The coefficient action is restriction of
  scalars through Γ(Spec A) ≅ A and the structural map. Thus the bases are actual
  monomials, not arbitrary bases of equally sized modules.
- The second conjunct covers every s⊆t and every monomial generator. The presheaf
  restriction sends that generator to the same exponent, with its enlarged support
  condition given by `laurentExponents_mono`. Linearity gives all section restrictions.
- `K` and the degreewise linear equivalences `g p` specify the alternating Čech terms:
  products over strictly increasing tuples, equivalent to subsets of size p+1.
  The next conjunct specifies the signed face-restriction differential exactly as
  in the recorded `Scheme.alternatingCechComputes`. Natural-number indexing means
  the complex is zero in negative degrees.
- `q` is an isomorphism of A-module cochain complexes from the categorical coproduct
  over `{e : Fin (n+1) → ℤ // ∑ i, e i = d}` of `exponentCechComplex n e` to K.
  This existing complex has basis `exponentCechBasis n e p`, precisely subsets of
  cardinality p+1 containing `exponentCechNegativeSet n e`, and the insertion-sign
  differential. The last conjunct specifies the image of each basis generator:
  its coefficient is a exactly on the same subset and exponent and zero elsewhere.
  It identifies the summands as the fixed-exponent subcomplexes of this very Čech
  complex, beyond merely asserting an abstract complex isomorphism.

Recorded dependencies read and used:
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist:
  `AlgebraicGeometry.ProjectiveSpace.twist` (definition and full docstring read).
  Also read the dependency record's `transitionUnit` in TransitionUnits and
  `nonempty_cechComplex_twist_iso_monomialCechComplex` in Cohomology.Serre.
  The latter assumes Field and uses full tuples, so it cannot replace this statement.
- Sheaf.AlgebraicGeometry.AlternatingCechComputes:
  `AlgebraicGeometry.Scheme.alternatingCechComputes`, read in full; its terms and
  signed restriction differential supply the alternating convention used here.
- The already landed node def-pc-exponent-cech-complex and its recorded module
  Sheaf.AlgebraicGeometry.ProjectiveSpace.ExponentCechComplex were read in full.
  Reused `exponentCechComplex` and `exponentCechBasis`. Added this landed node to
  stmt_deps under brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES).
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistSections:
  `twistMonomialSection`, `bijective_sum_twistMonomialSection` (CommRing, not Field),
  `twist_presheaf_map_twistMonomialSection`, and the standard-intersection descriptions.
  The section bases and restriction clauses already have upstream ingredients; the
  combined alternating direct-sum statement does not have an existing declaration.

Edge cases: zero ring is allowed, including the empty associated projective scheme;
all the free modules then vanish. No Nontrivial or Noetherian hypothesis is added.
Negative, zero, and positive d are all retained. For p>n there are no increasing
(p+1)-tuples and no exponentCechBasis elements, so both degree terms are zero.
For all nonnegative exponents, all nonempty subsets occur; for all negative exponents,
only the full coordinate set occurs. Empty s is intentionally excluded by the node;
the full coordinate set and singleton intersections are included. The condition n≥1
is retained even though the construction also makes sense in dimension zero.

Searches:
- msearch leanfinder, "sections of projective space twisting sheaf Laurent monomial
  basis alternating Cech decomposition": eight basic Proj/localization hits, no match.
- msearch loogle, "Finsupp, DirectSum": twelve hits including finsuppLEquivDirectSum;
  these identify free modules, not this geometric comparison.
- msearch grep, "Laurent|twistMonomial" in AlgebraicGeometry: zero Mathlib hits.
- msearch leansearch, "projective space twist Laurent monomial Cech complex decomposition":
  service unavailable (Internal Server Error).
- rg in WeilConjectures for monomial/Monomial/alternatingCech/projectiveSpaceTwist:
  found MonomialCech, TwistSections and Serre; inspected the signatures and constructions.
- rg for the item id in WeilConjectures and dag/lean_names_upstream.json: no matching tag.
- rg in lean/Sheaf for monomial/Laurent: found the landed ExponentCechComplex and
  ExponentCechHomology; used the former instead of duplicating its definition.

Source checked directly at https://stacks.math.columbia.edu/tag/01XS, proof of
Lemma 30.8.1: ordered terms, signed differential, exponent grading, and NEG(e) pieces.
The local literature checkout has only citation indexes, so the source was read online.
There is no statement correction or disputed statement.

Validation: lcompile.py compiled the module cleanly (2.4 seconds), with no warnings.

## Second reading by T1

Read the sandbox node and Lean side by side, independently of the worker's verdict.
Read the source TeX at `coherent.tex`, label
`lemma-cohomology-projective-space-over-ring`, through the proof's ordered terms,
exponent grading, and NEG(e) description. The repository has no local Stacks source;
retrieved the official Stacks GitHub TeX into this item's scratchpad and also read
https://stacks.math.columbia.edu/tag/01XS. The section's introduction identifies
projective space over Spec A with Proj A[T_0,...,T_n], compatibly with O(d).
The source assumes an arbitrary commutative ring, with no field, Noetherian,
nonzero-ring, or characteristic hypothesis. The source proof allows n=0; this
node deliberately asserts the n>=1 case, which the Lean retains.

Object/hypothesis/conclusion checklist (each verdict: matches):

1. A commutative ring A: `(A : Type u) [CommRing A]`. No additional algebraic
   instance is required. The structural coefficient map is the composite of
   `Scheme.ΓSpecIso (.of A).inv` and the projective-space structural map on
   global sections. `ModuleCat.restrictScalars` therefore gives the actual
   A-module of sections, not a module with an arbitrary scalar action.
2. Dimension n>=1 and integer d: `(n : ℕ) (hn : 1 ≤ n) (d : ℤ)`.
   The n+1 coordinates are `ULift.{u} (Fin (n + 1))`. This is a finite ordered
   set canonically equivalent to the node's coordinates, with no extra
   universe restriction on A. Exponent vectors in the coproduct use the
   unlifted `Fin (n + 1)` and the final clause translates by `ULift.up`.
3. P and O_P(d): `ℙ(ULift ...; Spec (.of A))` and the recorded dependency's
   `ProjectiveSpace.twist ... (Spec (.of A)) d`. Opened Twist.lean's definition
   and docstring, and TransitionUnits.lean's `transitionUnit`, which is the
   d-th power of x_i/x_j. These are precisely the relative model and twist
   chosen by def-pc-projective-space-twist and the project's PROJ TWISTS
   convention, with the Proj-model bridge reserved for stage 3.
4. Every nonempty subset J and its intersection U_J: the universal family
   `b : ∀ s : Set (ULift ...), s.Nonempty → ...` uses the preimage under
   `toProjInt` of `basicOpenInt ... s`. Read the upstream monomial basic-open
   membership criterion and `preimage_basicOpenInt_range`: these opens are
   the standard intersections, not arbitrary neighborhoods.
5. Free A-module with sum e_i=d and e_i>=0 outside J: the domain of `b s hs`
   is `laurentExponents s d →₀ A`. Opened Homogeneous.lean's
   `MvPolynomial.laurentExponents`, whose two predicates are exactly these.
   The `≃ₗ[A]` asserts both spanning and independence. The first conjunct
   fixes `Finsupp.single e a` to coefficient a times `twistMonomialSection`;
   read that section's definition as pullback of the actual homogeneous
   Laurent fraction on the integral model. Thus the asserted identification
   is by the named monomials, not merely an abstract free-module equivalence.
6. Every restriction for J subset J': the second conjunct quantifies s,t,
   their nonemptiness witnesses, `hst : s ⊆ t`, all allowed exponents and
   coefficients. The map is the twist presheaf's actual restriction along
   the reversed inclusion of opens; `laurentExponents_mono hst d e.2`
   retains e and enlarges its allowed denominator set. Equality on singles
   gives the full inclusion by linearity. Read the upstream restriction
   theorem and checked its inclusion direction, including s=t.
7. The alternating Cech complex on this cover: `K` and the degreewise
   linear equivalences `g p` give products of sections over strictly
   increasing (p+1)-tuples. Read the recorded declaration
   `Scheme.alternatingCechComputes` in full; its current signature uses a
   chosen-intersection `SiteCechComplex`. Here the concrete standard
   intersections are written directly and the same signed face formula
   specifies K's differential. `j.succAbove` deletes j, and the restriction
   is toward the larger intersection; the sign is `(-1 : ℤ)^j.val`.
   A finite tuple index set makes these products the source's finite sums.
   Natural-number indexing represents zero negative degrees.
8. Direct sum over all e with total d: `q` is a complex isomorphism from
   `∐ fun e : {e : Fin (n + 1) → ℤ // ∑ i, e i = d} ↦
   exponentCechComplex (A := A) n e.1` to K. This is a coproduct in module
   complexes, not a product over infinitely many exponent vectors.
9. The fixed-e degree-p basis and its inherited differential: opened the
   landed def-pc-exponent-cech-complex node and its entire module.
   `exponentCechBasis` is exactly the finsets J with card p+1 containing
   `exponentCechNegativeSet` (coordinates with e_i<0).
   `exponentCechDifferential` inserts k with sign counting j in J below k.
   For a sorted enlarged tuple that count is k's deletion position, so
   this agrees with the preceding face differential, including characteristic 2.
   The last conjunct evaluates the coefficient of w after applying the
   coproduct injection, q, g, and b.symm: it is a exactly at the same subset
   and exponent, and zero otherwise. Thus these summands are the actual
   fixed-exponent subcomplexes of the asserted Cech complex.

The three stmt_deps were opened, including all relevant recorded signatures.
The gained dependency def-pc-exponent-cech-complex is already landed and usable;
its addition is allowed by STMT_DEPS MAY GAIN LANDED NODES. The delivery introduces
no new definition node and no dependency module, so H12/H13 need no extra packet.
No statement correction or statement_change is present or needed.

Edge cases: empty J is excluded exactly by the node, while singletons and the
full coordinate set occur. The coordinate set is nonempty even at n=0, but hn
excludes n=0 exactly as the node does. The zero ring and hence empty projective
scheme are allowed; both coefficients and section modules then vanish.
There is no Nontrivial, field, Noetherian, or characteristic restriction.
All integer twists, including negative and zero d, are retained. For p>n
both strictly increasing tuples and subset bases are empty, giving zero terms.
When N_e is empty all nonempty subsets occur; when N_e is full only degree n
occurs. Infinite exponent indexing uses a coproduct, so only finitely many
coefficients occur in each cochain. All binders and the universe u are explicit;
ULift changes representation, not the set of cases covered.

Independent searches (with different queries from the first reader):

- msearch leanfinder: `ordered Cech complex polynomial localization splits by
  multidegree over commutative ring`: eight hits, including ordinary polynomial
  homogeneous decomposition and Dold-Kan summands, no geometric comparison.
- msearch loogle: `MvPolynomial.laurentExponents`: unavailable, unknown identifier
  in that service's Mathlib index. The declaration was read locally instead.
- msearch leansearch: `ordered Cech twist complex direct sum by exponent vectors`:
  service unavailable (Internal Server Error); no mathematical verdict inferred.
- msearch grep: `graded|weight|ordered`, then `NEG|multidegree|fixed.exponent`:
  broad results were unrelated. Targeted local rg on Mathlib/AlgebraicGeometry
  for Cech, Čech and Laurent found no matching statement.
- Local rg on the project and upstream for multidegree, exponent grading,
  Cech isomorphisms and laurentExponents found TwistSections, MonomialCech,
  Serre and the landed ExponentCechComplex. Read
  `bijective_sum_twistMonomialSection` (CommRing) and
  `twist_presheaf_map_twistMonomialSection`. Read `cechComplexTwistIso` and
  `nonempty_cechComplex_twist_iso_monomialCechComplex`: their linear geometric
  comparison requires Field and uses all tuples, rather than the alternating
  subset complex. MonomialCech's own implementation note likewise explicitly
  says its tuples are unrestricted. These are ingredients or other notions,
  not an existing declaration for the combined node's statement.
- Local rg for the item id and proposed full declaration in the upstream sources,
  dag/lean_names_upstream.json and lean/Sheaf found no existing realization.

H5/H6/H8/H9: the delivery declares one theorem with `by sorry` and no definitions,
private copies, local notation, local instances, hidden let/show binders, or
proved helper statements. The module and theorem docstrings identify the source
and blueprint node. The theorem's proof docstring follows all three node steps
and their dependencies. Imports supply the geometric ingredients, the recorded
alternating convention, and the landed fixed-exponent complex. All lines are
within 100 characters. The node's lean.statement was checked byte-for-byte against
the signature before `:= by`; it matches. Local lcompile succeeded in 2.4 seconds
with exit code 0 and no warnings.

Mismatches found: none. Changes: appended this independent second-reading section;
left the correct Lean, node statement, dependency records and worker report intact.
