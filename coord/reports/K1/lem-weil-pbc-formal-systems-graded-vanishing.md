## Worker report

The module `lean/Sheaf/AlgebraicGeometry/GradedSerreVanishing.lean` states
`AlgebraicGeometry.graded_serre_vanishing`, with `sorry` as its only proof.
The item statement is unchanged. One missing notion is supplied in a new definition node;
there are no dependency replacements or statement corrections.

Hypothesis and conclusion correspondence:

- Noetherian commutative A: `{A : Type u} [CommRing A] [IsNoetherianRing A]`.
- Finite type commutative A-algebra B: `{B : Type u} [CommRing B] [Algebra A B]
  [Algebra.FiniteType A B]`. FiniteType means finite algebra generation, not Module.Finite.
- The nonnegative grading: `β : ℕ → Submodule A B` and `[GradedAlgebra β]`.
  Mathlib's GradedAlgebra combines the internal direct-sum decomposition and graded
  multiplication. Its degree-zero piece contains the scalar image of A, as a graded
  A-algebra must, but is not required to equal A. No degree-one generators are specified.
- X and its proper map: `(X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsProper f]`.
- B tilde and its pullback: the new structure's `action` has source
  `pulledBackAssociatedAlgebra f ⊗ F`, where that module is literally the recorded
  tensorPullback applied to the recorded associatedModule of B. Scalar restriction along
  `(Scheme.ΓSpecIso (.of A)).hom.hom` views B as a module over Γ(Spec A,O).
- G: `(F : X.Modules) (M : PulledBackGradedModule β f F)` supplies its grading and
  action of this particular algebra, and `(hF : F.IsQuasicoherent)` is quasi-coherence of
  the underlying O_X-module. This is the quasi-coherent algebra-module convention on a
  scheme: locally the module is associated to a module over the affine algebra. No finite
  type condition on F as an O_X-module is imposed.
- Graded finite type: `(hM : M.IsFiniteType)` requires locally finitely many homogeneous
  generators in arbitrary integer degrees. The new predicate is local surjectivity, so it
  does not erroneously require sectionwise surjectivity on arbitrary opens. N-graded
  modules are included by setting the negative pieces to zero; integer grading allows
  every shift in the node, without any boundedness assumption.
- Invertible ample L: `(L : X.Modules) [L.IsInvertible]
  (hL : Scheme.Modules.IsAmple X L)` uses the recorded absolute ampleness definition.
- The single bound: `∃ d₀ : ℕ, ∀ (p d : ℕ), 0 < p → d₀ ≤ d → ...` is one bound
  independent of both the cohomological and homogeneous degrees. Taking a nonnegative
  bound is equivalent to the integer bound in the source for the nonnegative powers in
  the node: enlarge any integer bound to max(0,d0). No separate bound per graded piece.
- The twist: `(SheafOfModules.monoidalCategory X.sheaf).tensorObj F (L.tensorPow d)`
  is the existing sheafified tensor, and the existing tensorPow has zeroth power O_X.
  Writing the monoidal structure explicitly avoids instance inference on the definally
  equal ringed-space carrier of moduleCohomology.
- Vanishing: `IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (...))`.
  This is zero as a module, not IsZero on a bare type. Cohomology is the recorded right
  derived global-sections functor on O_X-modules, not the upstream abelian-sheaf Ext encoding.

Dependencies read and used:

- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing (all ideals finitely generated).
- Mathlib.AlgebraicGeometry.Morphisms.Proper: AlgebraicGeometry.IsProper;
  its IsSeparated, UniversallyClosed and locally-finite-type fields give properness,
  with quasi-compactness supplied by universally closed.
- Sheaf.AlgebraicGeometry.AssociatedModule: AlgebraicGeometry.associatedModule and
  associatedModuleCanonicalSection, their full signatures and canonical-section docstrings.
- Sheaf.AlgebraicGeometry.TensorPullback: AlgebraicGeometry.Scheme.Modules.tensorPullback;
  Sheaf.AlgebraicGeometry.TensorPullbackAdjunction:
  AlgebraicGeometry.Scheme.Modules.exists_tensorPullbackAdjunction, including the canonical
  tensor-unit section formula. Only a proof is chosen to supply that adjunction; the new
  definitions contain no sorry in data.
- Sheaf.AlgebraicGeometry.Coherent (pqf-def-coherent): its module documentation records
  Mathlib SheafOfModules.IsQuasicoherent, the part of that node used here.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  AlgebraicGeometry.Scheme.Modules.IsInvertible and tensorPow.
- Sheaf.AlgebraicGeometry.Ample: AlgebraicGeometry.Scheme.Modules.IsAmple, absolute
  ampleness, including CompactSpace and affine nonvanishing neighbourhoods.
- Sheaf.Paper.PQFCohomology: AlgebraicGeometry.sheafCohomologyAndHigherDirectImages
  identifies the shared cohomology functors. The statement uses
  Sheaf.Topology.RingedSpaceModuleCohomology: RingedSpace.moduleCohomology.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct: the recorded
  SheafOfModules.monoidalCategory comes from the imported upstream Monoidal module.
  The new action also uses WeilConjectures.AlgebraicGeometry.Modules.TensorSection:
  Scheme.Modules.tmulSection, the canonical sectionwise pure tensor map.

Edge cases checked before writing: zero rings, the empty scheme, F=0, the empty local
family (t=0), degrees with zero pieces, generators in negative degrees, B concentrated in
degree zero, and B generated in degree two. None is excluded. When X is empty the local
conditions and ample neighbourhood condition are vacuous and cohomology vanishes. For t=0
span of the empty set forces local zero, as a sheaf epimorphism from zero should. Degree
zero twist and p=0 are well typed; the theorem claims nothing at p=0. No positive
characteristic or field restriction occurs. All universes and variables are bound explicitly.
A common universe for the small rings, scheme and modules loses no mathematical case,
since different small universes can be lifted to their maximum.

Searches for an existing theorem (2026-10-11):

- msearch leanfinder: "Serre vanishing finite graded module proper scheme ample invertible
  sheaf": eight hits on qcqs sections/basic opens, Proj properness and projective resolutions;
  none gives the theorem.
- msearch loogle: "GradedAlgebra, GradedRing": zero hits.
- msearch grep: "Serre|graded.*vanishing" in AlgebraicGeometry: zero hits.
- rg of the upstream WeilConjectures tree for the item id, graded vanishing and
  graded_finiteness found no declaration; a graded prime-avoidance docstring is unrelated.
- rg of lean/Sheaf found ring-level graded-module lemmas and the homogeneous sheaf
  structures, but no graded Serre theorem. No proposed declaration name exists in
  Mathlib, upstream, the local library, or dag/lean_names_upstream.json.

The local Stacks coherent.tex is absent on this machine. Read the primary source online:
https://stacks.math.columbia.edu/tag/0897, Lemma 30.19.3 (2), including its full proof.
It says precisely the hypotheses and uniform conclusion here. The declaration docstring
carries all five steps of the node proof and the node ids needed at each step.

Validation: the definition module compiled cleanly in 2.5 seconds. After correcting duplicate
universe names in the combined scratch file and making the twist's monoidal structure
explicit, both modules compiled together cleanly in 3.6 seconds on the server.

## New nodes

`def-weil-pbc-pulled-back-graded-module`, module
`Sheaf.AlgebraicGeometry.PulledBackGradedModule`, supplies the actual pulled-back
associated algebra module, its canonical constant sections, a graded action on F, and
finite type via local homogeneous generators in arbitrary degrees. Its source is the
hypothesis of Stacks 0897 together with the already recorded associated-module and
module-pullback constructions. It reuses Mathlib GradedAlgebra, coproducts, RingHom,
End and Submodule.span, and the project associatedModule, canonical-section map,
tensorPullback and its canonical adjunction. No data is postponed.

Why the action data specifies precisely a module over the required algebra: the constant
sections 1 tensor b generate B tilde locally over O_Spec A, and after pullback generate
T locally over O_X. An O_X-linear tensor action is consequently determined by its values
on those sections. The `action_constant` equation pins them to `constantAction b`.
The ring-homomorphism laws give additivity, unit and associativity on these generators;
O_X-bilinearity extends those laws to T. In particular A scalar compatibility follows from
the associated-module tensor relation and this equation, so there is no free second algebra
structure or unrelated action. The coproduct decomposition imposes the actual sheaf grading,
and `graded` gives compatibility with β. Endomorphism multiplication is composition in
application order, so the RingHom multiplicativity is precisely the module-action law.

Why finite type matches shifted free generators: a section in piece δ defines a map from
T shifted by δ. The finite generating family defines their direct-sum map to F. Its image
is locally the O_X-span of constant B-actions on the generators because the canonical
B-sections generate T locally. The predicate says every local section locally belongs to
this span, exactly sheaf epimorphy. It neither imposes degree-zero generation nor finite
generation as an O_X-module. This definition is not a second copy of the landed
GradedSheafModule: that structure only treats nonnegative homogeneous families with an
arbitrary graded sheaf algebra and degree-zero generation, and provides neither the
specified f^* B tilde action nor arbitrary-shift finite type.

Searches: msearch LeanSearch for "graded finite type sheaf module over pullback of associated
algebra" was unavailable (Internal Server Error). LeanFinder for "finite type graded sheaf
module over pullback associated algebra with homogeneous generators arbitrary shifts"
returned eight graded-algebra/Proj/homogeneous-localization hits; none is the notion.
Loogle "SheafOfModules, RingHom" returned twelve presheaf sheafification declarations;
none is the notion. msearch grep "PulledBackGradedModule|GradedSheafModule|graded.*sheaf"
in Mathlib Algebra returned zero hits. rg of upstream found only a Proj twist TODO and
projective-space special cases. rg of the project found GradedSheafStructures with the
limitations just described. rg of DAG definition nodes found no required combined notion;
blueprint_refs.py search "graded sheaf" returned zero blueprint nodes. Exact new names
were also searched in Mathlib, upstream, lean/Sheaf and the upstream name registry with
no hits. The new node records these searches, their results, and its blueprint ancestry.

## Second reading by K1

The node introduces: a Noetherian commutative ring A; a finite type commutative graded A-algebra B with grading β and no standard-generation or B₀=A assumption; a proper scheme X over Spec A with morphism f; the pulled-back associated algebra; a quasi-coherent module F equipped with a pulled-back graded module structure M; finite type by local homogeneous generators in arbitrary integer shifts; an invertible ample module L; and one natural-number bound d₀ such that for every p,d with p>0 and d₀≤d, the higher O_X-module cohomology of F tensor L^d is zero. The Lean renders these respectively as `[CommRing A] [IsNoetherianRing A]`, `[CommRing B] [Algebra A B] [Algebra.FiniteType A B]`, `β : ℕ → Submodule A B` with `[GradedAlgebra β]`, `(X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsProper f]`, `M : PulledBackGradedModule β f F`, `hF : F.IsQuasicoherent`, `hM : M.IsFiniteType`, and `(L : X.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple X L)`. The conclusion is exactly the stated `∃ d₀ : ℕ, ∀ (p d : ℕ), 0 < p → d₀ ≤ d → IsZero ...`, using `RingedSpace.moduleCohomology` and the sheaf monoidal tensor with `L.tensorPow d`.

The empty index and zero cases are covered by the local finite-type predicate (including t=0 and F=0); empty X, degree-zero B, arbitrary negative shifts, n=0/p=0, and all characteristics remain well typed. No mismatch with the node or Stacks Lemma 0897 (2) was found. The explicit monoidal tensor removes ambiguity about the intended sheaf tensor, and the new pulled-back graded-module structure supplies the previously missing notion without hollow data.

I searched Mathlib, the upstream WeilConjectures tree, local `lean/Sheaf`, and DAG nodes using graded-vanishing, finite-type graded sheaf module, and pulled-back associated algebra queries. No existing declaration states this theorem or the combined notion. Both delivery modules compile together cleanly with `scompile.py`; all proofs are named `sorry` proofs only.
