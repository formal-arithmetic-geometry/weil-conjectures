## Worker report

Repair of the independent review of immutable head `a92b21c18b16`, points H3, H4,
and H8. The delivered module is
`lean/Sheaf/SixFunctors/EtaleGenericHomTriangle.lean`. Its main declaration is
`AlgebraicGeometry.Etale.etale_internalHom_pullback_triangle`; all helper
declarations belong to this same notion and are listed in `lean.declarations`.
The natural-language node statement and all its other fields are unchanged.
The delivery wrapper rebases the repaired packet on current `newtargets-dag`.

H3: the three arbitrary `CommShift` binders have been removed. The source and
target contravariant Hom shifts are now the explicit construction
`etaleInternalHomFlipCommShift`; the specialized instance applies it to
`ModuleCat.{u + 1} A`. The construction proceeds as follows:

1. `etaleInternalHomTensorShiftIso` has components from the existing canonical
   `commShiftDerivedTensorFlipObj`, naturally in the other tensor variable.
2. `etaleInternalHomSourceShiftIso` transports the tensor-Hom/shift adjunction
   along that tensor isomorphism using `Adjunction.rightAdjointUniq`, then
   composes with the canonical `commShiftDerivedHomObj`. This fixes the map by
   its adjunct, rather than choosing an isomorphism from an existence result.
3. `etaleInternalHomFlipRawShiftComponent` uses `shiftFunctorOpIso` to turn
   the opposite-category shift by n into the original shift by -n. It applies
   the preceding map and normalizes -(-n) to n. This is the signed source
   reindexing of `def-pur-hom-complex`, transported through the closed
   adjunction. The raw maps compose with the scalar discrepancy (-1)^(n*m).
4. `etaleInternalHomFlipShiftComponent` multiplies the raw map by the explicit
   scalar (-1)^(n*(n-1)/2). The integer identity q(n+m)=q(n)+q(m)+n*m cancels
   that discrepancy. It preserves the degree-one map and extends it
   coherently to every integer. The same scalar occurs on both comparison
   rows, so it does not change beta's shift square.
5. Named naturality and zero/addition coherence theorems supply the proofs
   needed to assemble `etaleInternalHomFlipShiftIso` and `CommShift`. Their
   docstrings identify the source and give their mathematical proof plans.

All these definitions have real data. The four coherence/naturality theorems
and the main triangle theorem have `sorry` proofs, as required for stage 2.
There is no `sorry` inside a definition. The construction is first made for a
category of coefficients B with explicit universes and the existing derived
monoidal hypotheses, then specialized to module coefficients. This avoids
expensive comparison of two concrete presentations of the monoidal instance;
it adds no hypothesis to the item. The discarded exploratory helper module is
outside `lean/` and is not part of the delivery.

Derived pullback retains `commShiftLeftDerivedUpperStar` from the explicit
import `WeilConjectures.SixFunctors.Etale.Derived.Shift`. The report in the
returned delivery incorrectly claimed that `sf_internalHom_triangulated`
supplied canonical instances: it only states existence on a different Hom
encoding. The repaired theorem neither chooses nor assumes its structures.
The earlier signed-shift attempt in the retained packet was ill typed and
exceeded the compiler limit; the current construction replaces that attempt.

H4: `lean.note` now explains both specialization choices accepted in substance
by the reviewer. `Etale.derivedHom` is `MonoidalClosed.internalHom`, the right
adjoint of the unbounded K-flat derived tensor. Under the standard equivalence
between sheaves valued in `ModuleCat A` and modules over the constant ring
sheaf, it is canonically the K-injective Hom-complex construction of
`derivedInternalHomOfUniverses`. This is a representation of the same RHom,
not a private replacement definition. The general recorded declaration is on
`SheafOfModules`, while this node uses `DerivedCategoryModule` throughout.
Likewise `Etale.leftDerivedUpperStarTensorIso` is the specialization of
`ringedTopoiCanonicalDerivedTensorPullback` to exact constant-coefficient
étale inverse image: it is the actual derived oplax tensor comparison,
computed on K-flat representatives by the ordinary tensor comparison.

H8: the main theorem's docstring gives all six node proof steps: exactness and
the two reversed rows; I, J, q and the chain comparison b_E; identification of
Q(b_E) with the evaluation transpose on K-flat representatives and then on all
objects; descent of contravariant naturality through localization; the signed
shift square with the same I, J, q; and the three triangle squares followed by
all three two-of-three implications. Every helper has a source/blueprint
docstring. The record `lean.statement` is the entire signature verbatim,
including its conclusion, rather than just its binders.

The comparison map remains the actual construction
`etaleInternalHomPullbackComparison A g K M`: `homEquiv` of
`derivedTensorHomAdjunction` applied to the inverse of
`leftDerivedUpperStarTensorIso` followed by the pullback of its evaluation
counit. No arbitrary map, `Nonempty` choice, or extra invertibility assumption
replaces it.

Every hypothesis and clause of the node is rendered as follows:

- Finite commutative A: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
- Arbitrary schemes and morphism: `{X X' : Scheme.{u}} (g : X' ⟶ X)`.
- Fixed arbitrary M in the ordinary unbounded category:
  `(M : DerivedCategoryModule A X)`. No boundedness, constructibility,
  perfectness, étaleness of g, or invertibility of the coefficient order is
  imposed.
- Distinguished input triangle: `(T : Triangle (DerivedCategoryModule A X))`
  and `(hT : T ∈ distTriang (DerivedCategoryModule A X))`.
- Derived tensor, Hom, and exact inverse image: the existing
  `derivedTensor`, `derivedHom`, and `leftDerivedUpperStar` APIs. Beta is the
  specified evaluation transpose, as detailed above.
- Reversed source row: `triangleOpEquivalence` reverses T, then
  `((RHom(X)[ModuleCat A]).flip.obj M).mapTriangle` applies contravariant Hom,
  and `(L((g)^*[ModuleCat A])).mapTriangle` applies derived pullback.
- Reversed target row: first apply pullback to T; reverse that triangle with
  `triangleOpEquivalence`; apply contravariant Hom with fixed second variable
  the pullback of M. This gives exactly the three displayed target objects.
- Three comparison components in their correct variance/order:
  `φ.hom₁ = beta_(T.obj₃)`, `φ.hom₂ = beta_(T.obj₂)`, and
  `φ.hom₃ = beta_(T.obj₁)`. The existential phi is a triangle morphism, so its
  `comm₁`, `comm₂`, `comm₃` impose all three comparison squares. The final
  square uses the shifted first component and the canonical shifts fixed
  above, including the reversed-triangle sign.
- The final three conjuncts are the implications that invertibility of
  components (3,2), (3,1), or (2,1), respectively, implies invertibility of
  component 1, 2, or 3. These cover each meaning of "any two".

Dependency declarations read and used:

- `def-weil-pbc-derived-categories`: `Etale.DerivedCategoryModule`, from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, reexported by the
  recorded `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
- `def-pur-derived-internal-hom`: the recorded
  `CategoryTheory.derivedInternalHomOfUniverses` from
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, represented here by
  `Etale.derivedHom` from `WeilConjectures.SixFunctors.Etale.Derived.Hom`;
  the specialization is justified above and in `lean.note`.
- `def-kun-derived-tensor`: `Etale.derivedTensor`, from
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`, and its adjunction
  `Etale.derivedTensorHomAdjunction` from `Derived.Hom`.
- `prop-weil-pbc-inverse-image-modules-exact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`, from
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`; exact
  étale pullback and `Etale.leftDerivedUpperStar` are the existing six-functor
  realization on these same constant-coefficient categories.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: the recorded
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.
  ringedTopoiCanonicalDerivedTensorPullback`, represented by the canonical
  `Etale.leftDerivedUpperStarTensorIso` from
  `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`.
- `def-weil-triangulated-category`: Mathlib `CategoryTheory.Pretriangulated`,
  `Triangle`, `distTriang`, `Functor.mapTriangle`, and
  `Pretriangulated.triangleOpEquivalence`.
- Canonical shift infrastructure: `Etale.commShiftDerivedTensorFlipObj` and
  `Etale.commShiftLeftDerivedUpperStar` in `Derived.Shift`, and
  `Etale.commShiftDerivedHomObj` in `Derived.AdjunctionShift`.

Edge cases checked: identity and arbitrary g; arbitrary or zero M; the zero
triangle and contractible triangles; the empty scheme; zero, positive, and
negative shifts; characteristic two and the zero coefficient ring. No case is
excluded. In particular, the Z/3 counterexample from the return cannot be
introduced by choosing a different shift structure: none is a theorem binder.
The canonical adjunction construction and its explicit coherent normalization
fix every component. In particular, at shift 2 the normalizing scalar is -1;
this cancels the discrepancy of composing the two raw degree-one shifts.

Searches (the retained original search log was inspected):

- `msearch.py ... leanfinder "evaluation induced derived internal Hom pullback
  comparison morphism of distinguished triangles"`: generic triangle/Yoneda
  hits; no statement of this canonical étale comparison.
- `msearch.py ... loogle "internalHom, Triangle, CommShift"`: no hits;
  `internalHom` was not recognized by the service.
- `msearch.py ... grep
  "internalHom.*(triangulat|shift)|(triangulat|shift).*internalHom" Mathlib`:
  no hits.
- `rg` in Mathlib, `WeilConjectures`, and the shared `lean/Sheaf` for RHom,
  `commShiftDerivedHomObj`, `ihomShiftIso`, first-variable Hom shifts, and the
  new declaration names: found the existing covariant Hom shift and derived
  tensor shifts, but no canonical contravariant Hom `CommShift` instance or
  the item theorem. The Orientation module's ad hoc shifted-unit construction
  was inspected; this delivery uses the direct canonical tensor shift and
  its adjunction mate instead. No Orientation definition is duplicated.
- The current node, all six statement dependency records and source
  signatures/docstrings, and Stacks `sites-cohomology.tex` at
  `lemma-RHom-triangulated` were reread. The shared item's non-lean fields
  agree with the saved packet; the source request for the item module
  confirms that it has not already landed.

No statement correction, new node, or dependency module is necessary. No
`STATEMENT-DISPUTED` remains. Compiler/preflight results are recorded below.

## Second reading by Q54

Repair self-check with the current node and full module open: the finite ring,
schemes, arbitrary morphism, M, T, and distinguishedness hypotheses coincide
with the node. Both rows reverse the first Hom variable in order K'', K, K'.
The components hom₁/hom₂/hom₃ have exactly that order, and `comm₃` uses the
canonical structure constructed from the tensor-Hom adjunction, with its
explicit quadratic sign normalization. The initially proposed all-integer
coherence on unnormalized source shifts was corrected during self-check:
their composition has a Koszul discrepancy. The integer q(n) normalization
cancels it while preserving the degree-one triangle map. Pullback uses
its existing global canonical shift. All three isomorphism implications are
present. Beta is still the evaluation transpose. The erroneous arbitrary
instance claims in the old report were removed, `lean.note` now justifies
both alternative concrete APIs, and the full six-step proof is in the
main docstring. Every universe is explicitly bound. This section records the
worker's repair self-check; the maintainer performs the independent review
specified by the brief.

## Verification

`scompile.py Q54 lem-sf-etale-generic-hom-triangle
lean/Sheaf/SixFunctors/EtaleGenericHomTriangle.lean` passed on the complete
repaired module, exit 0, with no diagnostics: sandbox check 35.1 seconds and
module check 11.6 seconds, within the prescribed per-file limit. An isolated
probe of the same canonical adjunction construction also passed, 10.1 and
9.5 seconds. No timeout limit was raised and no global build was run.

The first dry run passed as commit `4a0f0137a8` before the final self-check
added the explicit quadratic sign normalization. That change repairs the
all-integer coherence of the helper; the main theorem signature and its
canonical degree-one shift are unchanged. The final packet is recompiled and
checked again before push.

The final normalized module passed `scompile.py`, exit 0 with no diagnostics:
sandbox check 23.8 seconds, module check 17.5 seconds. The final self-check
also confirmed that only the node's `lean` field changed, its recorded full
signature matches the file, all five postponed proofs are named theorems,
and every Lean line meets the 100-column limit.

Final `deliver2.py Q54 lem-sf-etale-generic-hom-triangle --no-push` passed:
`OK (dry run): commit 587aa8d0e7 passes the preflight and compiles; nothing pushed`.
