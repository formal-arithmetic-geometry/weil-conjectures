## Worker report

Recorded the existing declaration
`AlgebraicGeometry.Etale.exists_normalization_of_isAlgClosed` in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum`, lines 121–167.
No module is written: the existing theorem has exactly the mathematical content of the node.
Its full signature and docstring, and its integral-closure construction, were read.
This is a stage-2 statement attachment, not a claim that the entire upstream proof-import
closure is sorry-free. No node statement or dependency list is changed.

Hypothesis and clause correspondence:

- The arbitrary affine base Z is `{S' : Scheme.{u}} [IsAffine S']`.
- K is `{K : Type u} [Field K] [IsAlgClosed K]`.
- The arbitrary point is `(g : Spec (.of K) ⟶ S')`.
- The existential affine integral normalization is `∃ (S'' : Scheme.{u})
  (_ : IsAffine S'') (_ : IsIntegral S'')`.
- Every local ring is integrally closed by
  `(_ : ∀ x : S'', IsIntegrallyClosed (S''.presheaf.stalk x))`.
  The domain part is already forced by `IsIntegral S''`: Mathlib's FunctionField module
  supplies `instance [IsIntegral X] {x : X} : IsDomain (X.presheaf.stalk x)`.
  Thus the assertion is exactly “integrally closed domain”, without losing its domain clause.
- Algebraic closedness of the function field is `(_ : IsAlgClosed S''.functionField)`.
- The morphism to Z and its integrality are `(π : S'' ⟶ S') (_ : IsIntegralHom π)`.
- The field embedding is `(i : S''.functionField ⟶ CommRingCat.of K)`.
  The function field has its Mathlib `Field` instance. A unital ring homomorphism between
  fields is necessarily injective (its kernel cannot contain 1), so this type is precisely
  a field embedding; no separate injectivity hypothesis or conclusion is needed.
- The lift g^nu is the explicit composite
  `Spec.map i ≫ S''.fromSpecStalk (genericPoint S'')`.
- The factorization is `(Spec.map i ≫ S''.fromSpecStalk (genericPoint S'')) ≫ π = g`.
  This is the node's equality with sides reversed and categorical composition order.
- The node's “in particular” dominance is intrinsic to this displayed lift: spectra of
  fields each have one point, and `fromSpecStalk` at the generic point sends that point
  to the generic point. Its image therefore has closure all of the integral scheme.
  Stating dominance separately would repeat an automatic consequence, not change content.

Dependency declarations read and used by the existing signature:

- def-weil-affine-spectrum and def-pc-scheme: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Scheme`, `Scheme.Hom`, Mathlib.AlgebraicGeometry.Scheme.
- def-weil-algebraic-closure: `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic;
  also inspected `IsAlgClosure` there and `AlgebraicClosure` in
  Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure. Only algebraic closedness is needed.
- def-pc-integral-scheme: `AlgebraicGeometry.IsIntegral`, Mathlib.AlgebraicGeometry.Properties.
- def-weil-finite-integral-morphism: `AlgebraicGeometry.IsIntegralHom`,
  Mathlib.AlgebraicGeometry.Morphisms.Integral (also read the recorded IsFinite signature).
- def-sc-function-field: `Scheme.functionField`, Mathlib.AlgebraicGeometry.FunctionField.
  The recorded Sheaf.AlgebraicGeometry.FunctionField module expressly directs the arbitrary
  integral-scheme clause to this existing generic stalk. Its component product is not needed.
- def-weil-pbc-normal-ring: `IsIntegrallyClosed`,
  Mathlib.RingTheory.IntegralClosure.IntegrallyClosed, with `IsDomain` as above;
  also read `Localization.AtPrime` in Mathlib.RingTheory.Localization.AtPrime.Basic.
  The node asks normality of local rings, rendered directly on stalks.

Edge cases checked: the affine base may be reducible, nonreduced, or have a noninjective
map of global sections to K; the existing construction takes integral closure in K and
thus factors through the image automatically. No dominance of g on Z is required.
For the empty affine base there is no such g, since Spec K is nonempty; this is an
empty hypothesis case, not an excluded input. No characteristic restriction, dimension
bound, finite-type assumption, or algebraicity assumption on K is introduced.
All objects use the common arbitrary universe u, matching the scheme category of the node.

Searches performed (msearch.py, group NE, this item):

- LeanFinder: “normalization affine scheme in algebraically closed field integral morphism
  algebraically closed function field” returned eight general normalization declarations,
  including instIsIntegralNormalization and instIsIntegralHomFromNormalization, no exact hit.
- Loogle: “Scheme.functionField, IsAlgClosed” returned no hits (unknown short identifier).
- LeanSearch: “normalization affine scheme algebraically closed field function field” was
  unavailable, Internal Server Error; no negative verdict is inferred.
- Mathlib grep: `exists_normalization_of_isAlgClosed|normalization.*[Aa]lg[Cc]losed`
  returned no hits.
- Source/project rg with that pattern found the exact upstream theorem at line 126 and
  its use at line 243; the project only had an unrelated curve-normalization theorem.
- Source grep for the node id returned no hit. The upstream name index had no hit for
  the theorem name; direct source inspection located it at the path already in the node.

Source checks: read Stacks morphisms.tex Tags 035H, 035I, 035L and
etale-cohomology.tex Tag 0F08 (final normalization reduction). Read the exact upstream
normalization theorem cited by the node. No statement fault or dispute was found.

Validation: on 2026-10-15, read the current published source using
`scompile.py --source WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum`.
Verified the recorded signature verbatim against upstream and checked that no field other
than `lean` differs from the repository node. The required
`deliver2.py NE lem-sbc-normalization-algclosed-field --no-push` printed
`OK (dry run)`: the existing-declaration server probe compiles and preflight passes except
for the second reading, which the independent second reader supplies. The previously
reported published import collision did not recur. Nothing was pushed; no local compiler
was run and no upstream source was modified.


## Second reading by NE

Independently read the sandbox node, all seven statement-dependency nodes, the
existing upstream theorem and its construction (lines 121–167), and the current
server source obtained with `scompile.py --source
WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum`.
The published signature agrees verbatim with `lean.statement`. No statement
correction, new node, dependency module, or Lean source change is needed.

Object/hypothesis/conclusion checklist, in the node's order:

1. An arbitrary affine scheme Z: `{S' : Scheme.{u}} [IsAffine S']`.
   Verdict: exact; neither reducedness nor integrality is imposed on Z.
2. An algebraically closed field K: `{K : Type u} [Field K] [IsAlgClosed K]`.
   Verdict: exact; no characteristic or algebraicity-over-another-field condition.
3. An arbitrary morphism g from Spec K to Z: `(g : Spec (.of K) ⟶ S')`.
   Verdict: exact; g need not dominate Z.
4. Existence of an affine integral scheme Z^nu:
   `∃ (S'' : Scheme.{u}) (_ : IsAffine S'') (_ : IsIntegral S'')`.
   Verdict: exact, including nonemptiness inherent in integral schemes.
5. An integral morphism pi to the original Z:
   `(π : S'' ⟶ S') (_ : IsIntegralHom π)`. Verdict: exact; not finite.
6. A field embedding of k(Z^nu) into K:
   `(i : S''.functionField ⟶ CommRingCat.of K)`. Verdict: exact.
   Mathlib FunctionField.lean defines this function field as the generic stalk
   and supplies its Field instance for integral schemes. CommRingCat morphisms
   are unital ring homomorphisms, hence automatically injective from a field.
7. Every local ring of Z^nu is an integrally closed domain:
   `(_ : ∀ x : S'', IsIntegrallyClosed (S''.presheaf.stalk x))`.
   Verdict: exact; the domain clause follows from the actual instance
   `[IsIntegral X] {x : X} : IsDomain (X.presheaf.stalk x)` at
   Mathlib.AlgebraicGeometry.FunctionField:178, independently of this theorem.
8. Algebraic closedness of k(Z^nu): `(_ : IsAlgClosed S''.functionField)`.
   Verdict: exact; its field structure is the canonical generic-stalk instance.
9. The specified lift induced by i and the generic-point morphism:
   `Spec.map i ≫ S''.fromSpecStalk (genericPoint S'')`. Verdict: exact.
   It is explicitly this composite, rather than an arbitrary existential lift.
10. Factorization g = pi composed with the lift:
    `(Spec.map i ≫ S''.fromSpecStalk (genericPoint S'')) ≫ π = g`.
    Verdict: exact; equality symmetry and categorical composition explain the order.
11. In particular the lift is dominant. Verdict: already forced by its displayed
    expression. Both field spectra have exactly one point; the point of
    `Spec S''.functionField` maps to `genericPoint S''` by
    `Scheme.fromSpecStalk_closedPoint` (Mathlib.AlgebraicGeometry.Stalk:102).
    Its image therefore contains a point whose closure is the whole space.
    No independent dominance assumption or weakened conclusion is hidden here.

Checked dependency interfaces directly in their source modules: Scheme and
Spec/Spec.map in Mathlib.AlgebraicGeometry.Scheme; IsAffine in AffineScheme;
IsIntegral in Properties; IsIntegralHom in Morphisms.Integral (extends
IsAffineHom with integral section maps); IsAlgClosed in FieldTheory.IsAlgClosed.Basic
(polynomial splitting, equivalent to roots of nonconstant polynomials);
IsIntegrallyClosed in RingTheory.IntegralClosure.IntegrallyClosed (integral
closedness in FractionRing). The algebraic-closure node is a Mathlib leaf: its
algebraically closed field clause uses IsAlgClosed, without requiring IsAlgClosure.
Read Sheaf.AlgebraicGeometry.FunctionField in full: its recorded component-product
definition expressly delegates the arbitrary integral-scheme clause to Mathlib's
Scheme.functionField. Thus using that generic stalk introduces no private copy
or curve, dimension, finite-type, or Noetherian restriction.

Source check: read morphisms.tex definition-normalization-X-in-Y (035H),
lemma-characterize-normalization (035I), and lemma-normal-normalization (035L),
including the surrounding hypotheses; also etale-cohomology.tex
lemma-base-change-does-not-hold (0F08) and its final normalization reduction.
The quasi-compact/quasi-separated requirements for relative normalization hold
here because g is a morphism between affine schemes. Spec K is normal with one
irreducible component, so the hypotheses of 035L are automatic. The integral
closure construction in the existing proof takes A -> K without requiring
injectivity, equivalently taking integral closure of its image. Its fraction
field is algebraically closed by the cited integral-closure fraction-field fact.
There is no missing global source hypothesis on this standalone normalization lemma.
The upstream module is reused as-is; source/blueprint docstring requirements for
new delivered modules do not require rewriting a read-only existing theorem.

Edge cases: empty affine Z admits no morphism from the nonempty Spec K; this
case is included vacuously. A zero base ring likewise admits no unital map into
K. Reducible and nonreduced affine bases, arbitrary kernel of A -> K, all
characteristics, and arbitrary transcendence degree are included. The index-set
and degree-zero checks have no extra parameter here. Universe u is declared in
the upstream module; schemes, function fields, and K belong to its arbitrary
common scheme universe. There is no fixed small universe or unbound variable;
ambient Λ, X, S, p from other declarations are absent from this signature.

Independent searches (2026-10-15): msearch LeanFinder query “affine integral
normal scheme lifting a geometric point through its generic point” returned
normalizationDesc, toNormalization, and general function-field declarations,
not a competing exact theorem. Loogle query “IsAlgClosed,
AlgebraicGeometry.IsIntegralHom” returned no hits. LeanSearch query “affine
scheme normalization in an algebraically closed geometric point” was unavailable
(Internal Server Error); no negative verdict inferred. Direct rg using
`normalization.*[Ff]ield|[Nn]ormalization.*closed|exists_normalization` over
Mathlib/AlgebraicGeometry, upstream WeilConjectures, and project lean/Sheaf found
the exact CurveTestDatum theorem and specialized curve/finite-extension material.
Those specialized declarations add finite-type or field-extension hypotheses and
do not replace this theorem. Read the exact hit, its proof, and the server copy.

Mismatches found: none. Changes: appended this independent second reading only;
retained the existing-declaration record, mathematical statement, and dependencies.
Validation: delivery dry run and its server existing-declaration probe are run
below before pushing. There are no delivered Lean modules requiring sibling compiles.
