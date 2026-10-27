## Worker report

Item: `lem-pur-derived-injective-cone-comparison`, Q102, stage 2, 2026-10-22.
Module: `Sheaf.CategoryTheory.Abelian.DerivedInjectiveConeComparison`.
Main declaration: `CategoryTheory.rightDerived_injectiveRow_triangleComparison`.

The module states the entire node in five named theorems, each with proof `sorry`,
and one helper definition with real data. No statement correction, new DAG node,
or dependency repair is needed. The existing cone, comparison isomorphism, quotient,
unit, inverse unit and boundary are used directly. `boundedBelowRowTriangle` simply
packages the existing boundary with the two localized row maps as `Triangle.mk`.
It defines no new boundary, cone or derived functor.

Source read: `literature/stacks-project/derived.tex`, definition-cone (lines
2470 onward); section-canonical-delta-functor, Tags 014Z/0152 (lines 3900 onward),
including the displayed triangle with negative projection and its naturality proof;
lemma-injective-acyclic, Tag 05TH (lines 6948 onward). The existing boundary
comparison module was read in full, including the canonical definitions and proof.
The example Sheaf CompactObject module is withdrawn on this base; its node points
to `WeilConjectures.CategoryTheory.CompactObject`, whose header and definition were read.
No repair note for this item exists on the read base.

Hypotheses and objects, clause by clause:

- Abelian categories A and B: `{A : Type u₁} {B : Type u₂}` with
  `[Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]`.
  All object, morphism and localization universes are explicitly declared and independent.
- Enough injectives in A: `[EnoughInjectives A]`; no such assumption on B.
- Additive T: `(T : A ⥤ B) [T.Additive]`. No left exactness, preservation of
  injectives, or preservation of arbitrary quasi-isomorphisms is assumed.
- Derived categories in chosen morphism universes: `[HasDerivedCategory.{w₁} A]`
  and `[HasDerivedCategory.{w₂} B]`, the size structures of the dependency node.
- Bounded-below complexes and their row: `H : ShortComplex (CochainComplex.Plus A)`.
  E,F,G are exactly `H.X₁.obj`, `H.X₂.obj`, `H.X₃.obj`; u,v are `H.f.hom`, `H.g.hom`.
  `CochainComplex.Plus` means strictly zero terms below some integer, not just
  bounded-below cohomology.
- Termwise injectivity: the three separate binders
  `[∀ n : ℤ, Injective (H.Xᵢ.obj.X n)]` for i=1,2,3.
- Degreewise short exactness: `hH : (H.map (CochainComplex.plus A).ι).ShortExact`.
  For complexes in an abelian category, short exactness is precisely degreewise
  short exactness. The termwise-image hypothesis is `hTH` on the further map by
  `T.mapHomologicalComplex (.up ℤ)`.
- P is exactly `mappingCone H.f.hom`. Its Mathlib data give the two biproduct
  summands and differential, with the shifted E summand first internally;
  swapping the displayed ordering changes no morphism or sign. No arbitrary
  complex, map, or choice substitutes for P.
- q is exactly `mappingCone.descShortComplex (H.map (CochainComplex.plus A).ι)`;
  its two components are v and zero. q_T is the same construction on the image row.

Conclusions, clause by clause:

- `rightDerived_injectiveRow_coneComparison` asserts
  `CochainComplex.plus A (mappingCone H.f.hom)` and
  `∀ n, Injective ((mappingCone H.f.hom).X n)`.
- The canonical chi is the already constructed complex isomorphism
  `mappingCone.mapHomologicalComplexIso H.f.hom T`, not a supplied or chosen map.
  The theorem states `T(inr) ≫ chi.hom = inr_T` and
  `T(negativeProjection) ≫ T.commShiftIso.hom = chi.hom ≫ negativeProjection_T`.
  Here the negative projections are `(mappingCone.triangle ...).mor₃`; the
  Mathlib definition uses the right-shifted cocycle `-mappingCone.fst`.
  Thus the required `T(E[1]) ≅ T(E)[1]` is the canonical `commShiftIso` of the
  termwise complex functor and is included in the asserted equation.
- The same theorem states `QuasiIso q`, `QuasiIso q_T`, and
  `chi.hom ≫ q_T = T.map q`. The required isomorphism chi exists as actual data
  in Mathlib before any theorem in this delivery is used.
- `boundedBelowRowTriangle H hH` has maps `Q⁺u`, `Q⁺v` and
  `boundedBelowSESBoundary H hH`. The latter definition uniquely lifts the
  existing `DerivedCategory.triangleOfSESδ` across the fully faithful inclusion,
  with the endpoint quotient-factorization isomorphisms. `triangleOfSESδ` is
  definitionally `inv (Q.map q) ≫ Q.map negativeProjection ≫ Q.commShiftIso.hom`.
  This is precisely the node's cone-to-quotient boundary, including its sign.
- `rightDerived_injectiveRow_triangleComparison` asserts that this triangle is
  distinguished, that its RT-image is distinguished, and that there exists a
  triangle isomorphism e from that image to `DerivedCategory.triangleOfSES hTH`
  with `e.hom.hom₁`, `hom₂`, `hom₃` equal respectively to
  `boundedBelowInjectiveComparison T H.X₁`, `... H.X₂`, `... H.X₃`.
  This existing comparison is exactly the inverse derived unit followed by
  the localization quotient factorization. Since these are the components of
  an isomorphism, they are invertible; this also states invertibility of the
  original units after cancelling the quotient-factorization isomorphisms.
  These components fix the comparison uniquely: triangle morphisms, and thus triangle
  isomorphisms, are determined by these three components.
- In particular e is an isomorphism of triangles, not merely of their vertices
  or cohomology. `TriangleMorphism.comm₃` is exactly the last-arrow square with
  the canonical shift comparison of `T.rightDerivedFunctorPlus ⋙ Plus.ι`, because
  `Functor.mapTriangle` includes that comparison in its third arrow.
- The target is displayed after `DerivedCategory.Plus.ι`, so Mathlib's canonical
  `triangleOfSES` can be used directly. This inclusion is fully faithful and
  triangulated, reflects distinguished triangles, and all displayed vertices
  are in its image: T preserves strict lower bounds since it is additive.
  Consequently this is exactly the same assertion about triangles in D⁺(B),
  with no change of objects or additional size restriction.
- `rightDerived_injectiveRow_coneQuotient` gives a proof hP of boundedness of
  the fixed explicit cone, asserts `IsIso (alpha_P)`, and states
  `Q(TP) → Qh(TP) →[alpha_P] RT(QP) →[RT(Qq)] RT(QG) →[c_G] Q(TG)
   = Q(chi.hom) ≫ Q(q_T)`.
  The first arrow is the inverse canonical quotient factorization. Since
  alpha_P and the factorization are invertible, this is exactly the claimed
  identification of RT(Qq). It avoids assuming injectivity of T(P).
  The target's third arrow is exactly the existing `triangleOfSESδ hTH`, whose
  definition is the negative projection after inverse Q(q_T), with Q's shift
  comparison. No arbitrary representative of that arrow is used.
- `rightDerived_injectiveRow_naturality` quantifies over H,H' satisfying all
  the same assumptions and a strict row morphism `φ : H ⟶ H'`. Its first two
  equations give the two summand restrictions of the exact existing
  `mappingCone.map`: f on the F summand, e on the shifted E summand, and no
  off-diagonal term. The next equations are `C ≫ q' = q ≫ g`,
  `C ≫ negativeProjection' = negativeProjection ≫ e[1]`, and
  `T(C) ≫ chi' = chi ≫ C_T`. Its final three equations are naturality of each
  inverse-unit component with respect to e,f,g.
- `rightDerived_injectiveRow_triangleNaturality` makes the full triangle
  assertion explicit: for any e,e' with the prescribed inverse-unit components,
  there is a source triangle morphism psi with components Q⁺e,Q⁺f,Q⁺g,
  and `RT.mapTriangle.map psi ≫ e'.hom = e.hom ≫ triangleOfSES.map ... φ`.
  The target row morphism is the existing canonical Mathlib construction.
  Together with the preceding diagonal cone formulas, this renders the final
  naturality clause in full, not only at the level of objects.

Dependency declarations used (all recorded interfaces were usable):

- def-sp-abelian: `Mathlib.CategoryTheory.Abelian.Basic`, `CategoryTheory.Abelian`.
- def-sp-injective-resolutions: `Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
  `CategoryTheory.Injective` and `EnoughInjectives`. The recorded
  `InjectiveResolution` structure in `.Injective.Resolution` was read; the item
  does not choose or use resolutions.
- def-sp-left-exact-additive: `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`,
  `CategoryTheory.Functor.Additive`. Only the additive clause is needed, exactly
  as the node says. The `rightDerived` and `isoRightDerivedObj` signatures in
  `.Abelian.RightDerived` were also read and do not supply this whole statement.
- def-weil-pbc-bounded-derived-subcategories:
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`, `DerivedCategory.Plus`.
- def-weil-abstract-derived-category: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q` and its shift structure.
- lem-weil-pbc-right-derived-plus-injective:
  `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
  `Functor.rightDerivedFunctorPlus`, `Functor.rightDerivedFunctorPlusUnit`,
  the derived-functor instance, and injective-complex unit isomorphism instance
  in `DerivedCategory.DerivabilityStructureInjectives`. Their signatures and
  docstrings were read. The upstream extension
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
  supplies the already canonical shift and triangulated structures; it is
  publicly imported by the following module.
- lem-sc-p1-right-derived-injective-boundary:
  `WeilConjectures.CategoryTheory.Abelian.RightDerivedInjectiveBoundary`,
  `boundedBelowInjectiveComparison`, `boundedBelowSESBoundary` and
  `rightDerived_injectiveComplex_boundary`. Public import is needed because
  its two canonical constructions occur in our signatures, in addition to
  its theorem being a proof dependency.
- lem-pc-cone-short-exact-quasi-iso:
  `Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`,
  `CochainComplex.mappingCone.quasiIso_descShortComplex`. This module supplies the quotient and quotient-comparison identities in our
  signatures, so its import is public; the proof uses its quasi-isomorphism theorem.

Edge cases checked before writing: zero rows, split rows, identity row morphisms,
zero row morphisms and shifts of any strict lower bound all retain the same
cone and negative projection. Nothing requires a lower bound of zero, a nonzero
object, a nonzero functor, or injectives in B. Additive functors that fail left
exactness remain allowed; only the explicitly stated image-row exactness is
used. Independently sized A,B and derived morphisms remain allowed. The cone's
N-1 bound covers the shifted E summand even when F and G are zero.

Searches actually run:

- `msearch.py ... leanfinder`, query "A right derived additive functor compares
  the cone quotient triangle of a short exact row of bounded below injective
  complexes using its unit and canonical shift comparison": 8 hits, including
  `DerivedCategory.triangleOfSESIso` and `mappingCone.mapTrianglehIso`.
  They give partial cone/SES comparisons, not the full inverse-unit comparison.
- `msearch.py ... loogle`, query `"mapHomologicalComplexIso", "mappingCone"`:
  3 hits, including the canonical complex isomorphism and its quotient equation;
  reused, with their full source signatures read.
- `msearch.py ... grep`, query
  `mapHomologicalComplexIso|mappingCone.*plus|plus.*mappingCone` in `Algebra/Homology`:
  11 hits in MappingCone, Pretriangulated, ShortExact and Ext/Map. Sources read.
- `msearch.py ... leansearch`, query "Right derived units identify cone quotient
  triangles of bounded below injective complexes naturally in short exact rows":
  8 hits, including ordinary rightDerived, resolution evaluation/naturality,
  totalRightDerivedUnit and triangleOfSESIso. No whole-item match.
- `rg` in upstream `WeilConjectures/` and project `Sheaf/` for
  `boundedBelowSESTriangle|boundedBelow.*Triangle|Plus.*triangleOfSES|triangleOfSES.*Plus|injective.*cone.*comparison|rightDerived.*cone`:
  only unrelated partial matches (horseshoe single-object comparisons, derived
  colimits, etc.). The explicit mappingCone searches found existing signed-fibre,
  Roos and internal-Hom cone constructions, not this additive generic row theorem.
- `rg` for the node id in upstream `WeilConjectures/`: no match.
- `rg` for all proposed declaration names in Mathlib, upstream, project and
  `dag/lean_names_upstream.json`: no collisions. No new independent mathematical
  notion was needed: the helper only packages the node's own specified triangle.

Validation: all compiles use prescribed `scompile.py`, never a local or global
build. A compiler error in image-row morphism construction was repaired by
mapping the underlying row using `T.mapHomologicalComplex` directly, whose
zero-preservation instance is available. No new instance or assumption was
introduced. The complete file now compiles cleanly in both sandbox and library
module mode through scompile.py, with no errors or unexpected warnings.
Preflight and a fresh compile use the required delivery dry run. Every variable and
universe is explicitly bound, and `autoImplicit` is disabled. Every theorem has
exactly `sorry`; the sole definition has fully specified data.

## Second reading by Q102

The dispatch brief instructs this worker to deliver directly, prohibits starting
other agents, and assigns independent delivery review to the maintainer. This
section records my final source/interface cross-check; it does not claim review
by an independent worker.

I checked the node against the module again, in particular the points where an
objectwise or unsigned comparison would be insufficient. The cone comparison
is Mathlib's actual isomorphism; its negative-projection equation includes T's
shift comparison. The source boundary is the existing uniquely lifted canonical
SES boundary, not a newly chosen connecting map. The main result is a triangle
isomorphism with all three components fixed, so its last-arrow square includes
RT's shift comparison. The cone quotient equation uses the forward alpha_P,
explicitly asserts its invertibility, and inserts the quotient-factorization
isomorphism in the correct direction. Target triangleOfSESδ fixes exactly the
negative-projection/inverse-quotient arrow requested. The row naturality theorem
first identifies the diagonal cone map on each summand and its quotient and
negative-projection squares; the final theorem then states naturality as an
actual equality of triangle morphisms. The inclusion into D(B) is fully faithful
and reflects the D⁺ triangle assertion; it imposes no extra universe relation.

No mathematical mismatch or statement dispute was found. I added the final
triangle-morphism equality to make the node's naturality clause explicit and
checked the image-row morphism through the underlying cochain-complex functor. All five postponed theorems are clauses
of this node and have source/proof docstrings; no unrelated theorem is postponed.
