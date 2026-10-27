## Worker report

The delivery states `AlgebraicGeometry.finite_injective_section_affine_charts` in
`Sheaf.AlgebraicGeometry.FiniteInjectiveSectionAffineCharts`, with the proof postponed.
There are no new definitions and no statement correction.

The field is `{k : Type u} [Field k]`. The schemes are `{X Z : Scheme.{u}}`, the given
structure morphisms are `a : X ⟶ Spec (CommRingCat.of k)` and `b : Z ⟶ Spec
(CommRingCat.of k)`, and the given map is `q : X ⟶ Z`. The commutative triangle is
`hcomp : q ≫ b = a`. Finite type of a is the prescribed pair `[LocallyOfFiniteType a]`
and `[QuasiCompact a]`; finite and surjective q are `[IsFinite q] [Surjective q]`. The
section-map injectivity hypothesis is `hinj : ∀ V : Z.Opens, IsAffineOpen V →
Function.Injective (q.app V).hom`.

The Noetherianity conclusion for X is `IsLocallyNoetherian X ∧ CompactSpace X`.
The finite affine open cover is an existential natural number n and a family
`V : Fin n → Z.Opens`, with every member `IsAffineOpen` and supremum equal to top.
For every affine open W, `IsAffineOpen (q ⁻¹ᵁ W)` is the affineness of its inverse
image. Its coordinate ring is literally Γ(X, q ⁻¹ᵁ W); the target coordinate ring is
Γ(Z,W). The injection `(q.app W).hom` is the identification with its image subring,
and `hcomp` makes this canonical map compatible with the k-structure maps. Thus
its image is a k-subalgebra, without choosing an arbitrary embedding or algebra
structure. `(q.app W).hom.Finite` says exactly that the source section ring is a
finite module over the target section ring. Finite type of B and A over k is
`RingHom.FiniteType ((a.appLE ⊤ (q ⁻¹ᵁ W) le_top).hom.comp
(Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)` and the analogous b-map in the
signature. These are the canonical field-algebra maps, using Γ(Spec k) ≅ k. The
equality between the two compositions explicitly renders the k-subalgebra compatibility. Finally `IsNoetherianRing Γ(Z,W)` is Noetherianity of A.

Dependency declarations used: `Field` (Mathlib.Algebra.Field.Defs); `Scheme`, `Spec`,
`Scheme.Hom.app` and `Scheme.Hom.appLE` (Mathlib.AlgebraicGeometry.Scheme);
`LocallyOfFiniteType` (Mathlib.AlgebraicGeometry.Morphisms.FiniteType),
`QuasiCompact` (Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact), `IsFinite`
(Mathlib.AlgebraicGeometry.Morphisms.Finite), `Surjective`
(Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap), `IsLocallyNoetherian`
(Mathlib.AlgebraicGeometry.Noetherian), `RingHom.FiniteType`
(Mathlib.RingTheory.FiniteType), `RingHom.Finite`/`Module.Finite`
(Mathlib.RingTheory.Finiteness.Defs), and `IsNoetherianRing`
(Mathlib.RingTheory.Noetherian.Defs). All are the existing recorded dependency
notions. The module compiles through the prescribed scompile.py against the live
published server library (2026-10-24), both sandbox and library path, with no errors
or warnings beyond the expected sorry warning.

Edge cases: Fin 0 permits the empty affine cover. No nonemptiness condition is
placed on X, Z, any affine open, or any section ring, so empty schemes and the zero
coordinate rings of the empty affine open remain included. The identity morphism
case has the usual finite-type field affine charts. No separatedness or reducedness
condition was added; injectivity is imposed only on affine opens, as in the node.

Searches: repository rg searches over both lean/WeilConjectures and lean/Sheaf for
finite/injective sections, finite affine covers, and the finite-type/Noetherian
classes found the canonical Mathlib interfaces and sibling uses, but no theorem
stating this assembly. Mathlib searches in AlgebraicGeometry found the declarations
of Scheme.Hom.app/appLE, IsFinite.finite_app and IsAffineOpen.preimage, which give
only individual clauses. The node's recorded LeanFinder/Loogle/grep searches also
find these inputs but no exact existing assembly. No node faults or disputed
statement were found.

The current searches run through msearch.py on 2026-10-24 were:

- LeanFinder: "A finite surjective scheme map with injective affine section maps
  from a finite type scheme over a field has finite type Noetherian affine
  coordinate rings". Eight hits: IsFinite.finite_app, Scheme.Hom.finite_app,
  isFinite_iff, IsFinite.toIsAffineHom, Scheme.Hom.finiteType_appLE, and related
  finite-type interfaces. These are inputs, not the whole assembly.
- Loogle: "AlgebraicGeometry.IsFinite, AlgebraicGeometry.LocallyOfFiniteType".
  Six hits, including IsFinite.instLocallyOfFiniteType and the equivalence with
  integral plus locally finite type. None descends finite type to the target.
- Mathlib grep in AlgebraicGeometry:
  "(finiteType|finite_type).*(surjective|injective)|(surjective|injective).*(finiteType|finite_type)".
  Six hits in SpreadingOut, QuasiFinite, RationalMap, LocalFlatDescent and
  ClosedImmersion. Flat descent requires flatness, absent here.
- LeanSearch: "Descent of finite type over a field along a finite surjective
  scheme map injective on all affine coordinate ring sections". Eight hits,
  including RingHom.FaithfullyFlat.codescendsAlong_injective, IsFinite.recOn and
  IsFinite.instLocallyOfFiniteType; no exact assembly.
- Repository rg over lean/WeilConjectures, lean/Sheaf, and
  dag/lean_names_upstream.json for the node id and full declaration name found
  no existing declaration. Keyword searches for finite/injective sections and
  affine covers found distinct results and the recorded Mathlib inputs.

The statement dependency modules are public imports. The already-stated proof
inputs are also imported: QuasiCompact for the finite affine cover,
FiniteType for the affine-pair characterization, Noetherian for local
Noetherianity, Finite for finite inverse images, and Adjoin.Tower for
fg_of_fg_of_fg (Artin--Tate). Spectrum.Prime.Noetherian and Topology.NoetherianSpace
are plain proof imports for the remaining clauses of the affine-Noetherian input.
The six-step docstring names the DAG inputs and describes the finite-cover,
image-subalgebra, generator-lifting and zero-ring arguments.

Source checks read algebra.tex lemma-Artin-Tate (Tag 00IS),
lemma-Noetherian-permanence (Tag 00FN), and morphisms.tex
lemma-locally-finite-type-characterize (01T2), lemma-finite-type-noetherian
(01T6), and definition-integral (01WH). The current blueprint was read at
literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/, including the unit statement and proof. This node is
an auxiliary chart assembly; it does not change the blueprint unit.

Final validation: the revised module compiled independently via scompile.py at
both sandbox and library module names. The dry run passed preflight and the
per-file compile. Only the item's lean field is changed; no dependency module
or new node was necessary. The maintainer supplies the independent review.

## Second reading by Q152

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
