## Worker report

The delivery states `AlgebraicGeometry.IsAbelianVariety.exists_dual_polarization_calculus`
in `Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus`. Its sole proof is
`sorry`; its docstring contains all fourteen steps of the node's accepted proof plan.
The module `Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum` supplies the
missing definition interface, with actual module, morphism, and comparison constructions.
There is no chosen dual variety or line module manufactured from an unproved existence.
The item's mathematical statement, source, proof and proof dependencies are unchanged.

Hypotheses and clauses, in the order of the node:

* Algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]`.
* Abelian variety over that field: `A : Over (Spec (.of k))`, `[GrpObj A]`,
  `[IsAbelianVariety A]`. These are the recorded upstream objects, not a substitute category.
* Representation by an abelian variety with universal Poincare line: the existential
  `D : AbelianDualPoincareDatum A`. Its `dual`, `group`, `abelian`, `poincare` and
  `invertible` fields give precisely those objects and structures.
* Dimension: `IsAbelianVariety.dim D.dual = IsAbelianVariety.dim A`.
* Algebraic triviality on EVERY geometric fibre: `geometricFibres`, using
  `IsFibrewiseAlgebraicallyTrivial`, tests every algebraically closed `Ω : Type u`, every
  `s : Spec Ω ⟶ Spec k`, and every `t : Over.mk s ⟶ T`. The comparison is
  `AreAlgebraicallyEquivalent` on `Over.mk (pullback.snd A.hom s)`, so algebraic equivalence
  is taken over Ω, not over k. The generating smooth connected parameter varieties and
  the equivalence-relation closure are the existing `LineAlgebraicEquivalence` definitions.
* Rigidification and the isomorphism-class quotient: `D.rigidification` is an actual
  identity-axis isomorphism. `D.universal` quantifies over all schemes T, invertible M,
  fibrewise trivial M, and every actual rigidification r, and asserts `∃! f` for which
  there is an isomorphism i satisfying the rigidification equation. Existence and uniqueness
  of such f is exactly the bijection on rigidified isomorphism classes. Pullback is the
  actual canonical scheme-module inverse image; uniqueness gives parameter naturality.
* Both identity axes: `D.rigidification` handles `0 × D` and `D.otherAxis` handles `A × 0`.
  `D.tensorGroupLaw` fixes addition on the dual to mean tensor product of classified
  families; the group structure is not allowed to be unrelated to the representing object.
* Every invertible L: `∀ L : A.left.Modules, L.IsInvertible → ...`.
* The family and its homomorphism: `∃! φ, IsMonHom φ ∧ ClassifiesAbelianDifference D L φ`.
  The latter definition is the isomorphism `(1 × φ)^* P ≅ N_L` with
  `N_L = m^*L ⊗ p₁^*(Lᵛ) ⊗ p₂^*(Lᵛ) ⊗ c^*(0^*L)`.
  This is exactly the node's harmless constant-line normalization, explicitly described
  in its accepted proof step 2. Here m is `μ[A]`, the projections are `fst` and `snd`,
  c is `toUnit`, and the identity section is `η[A]`. `Scheme.Modules.dual` is the
  recorded sheaf Hom to the unit. No arbitrary maps replace these constructions.
* Point formula: for each k-point x, the second conjunct after homomorphism existence
  identifies the Poincare fibre at `x ≫ φ` with `t_x^*L ⊗ Lᵛ`. Translation is the
  explicit cartesian lift `(1,x)` followed by `μ[A]`. The constant identity-line factor
  becomes a one-dimensional constant line over k and hence may be omitted up to isomorphism.
* Every b in A(k): the next conjunct says the SAME φ classifies the normalized difference
  of `t_b^*L`. Existence/uniqueness of its classifying homomorphism makes this precisely
  `φ_(t_b^*L) = φ_L`.
* Every homomorphism a:B→A: the next conjunct quantifies over B with the same abelian
  variety structure, any normalized representing datum E for B, and a with `IsMonHom a`.
  It supplies a unique homomorphism `aDual : D.dual ⟶ E.dual` characterized by
  `(a × 1)^*P_A ≅ (1 × aDual)^*P_B`, and states
  `φB = a ≫ φA ≫ aDual` for the maps classifying L and its pullback. This is the
  categorical composition order of the node's `a^∨ φ_L a`.
* Inversion: the displayed Poincare-family isomorphism for `ι[A] ▷ D.dual` and
  `A ◁ ι[D.dual]` says that inversion is its own dual, by the preceding uniqueness.
  The next conjunct says that the same φ classifies `[-1]^*L`, which is exactly
  `φ_([-1]^*L) = φ_L` by uniqueness.
* Effective Cartier divisor and O(F): `J : A.left.IdealSheafData`, `J.IsInvertible`,
  and `Scheme.Modules.dual J.toModules`. The existing effective-Cartier interface
  identifies invertibility of this ideal with a closed subscheme locally cut out by
  one non-zero-divisor, and its dual is the recorded associated divisor line module.
* The final equivalence is `IsAmple A.hom (dual J.toModules) ↔ IsIsogeny φ`.
  The upstream `IsIsogeny` extends `IsMonHom`, surjectivity and finiteness of
  `(GrpObj.ker φ).hom`, so the whole scheme-theoretic kernel, including infinitesimal
  structure, is used.

Dependency declarations read and used:

* `Field` in Mathlib.Algebra.Field.Defs and `IsAlgClosed` in
  Mathlib.FieldTheory.IsAlgClosed.Basic (the dependency's recorded algebraic-closure notion).
* `AlgebraicGeometry.IsAbelianVariety` and `.dim` in
  WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs.
* `AlgebraicGeometry.Scheme.Modules.IsInvertible` in
  WeilConjectures.AlgebraicGeometry.Modules.Invertible, with the module tensor structure;
  `Scheme.Modules.dual` in WeilConjectures.AlgebraicGeometry.Modules.Dual.
* `IdealSheafData.IsInvertible.isInvertible_dual_toModules` in
  WeilConjectures.AlgebraicGeometry.EffectiveCartier; the recorded definition
  `IsEffectiveCartierCenter` and its equivalence with the invertible kernel ideal.
* `AlgebraicGeometry.IsAmple` in WeilConjectures.AlgebraicGeometry.Modules.VeryAmple.
* `AlgebraicGeometry.IsIsogeny` in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
* `Scheme.Modules.AreAlgebraicallyEquivalent` in
  Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence (already landed definition node).
* Canonical Mathlib `Scheme.Modules.pullback`, `pullbackComp`, `pullbackCongr` and the
  upstream `pullbackObjUnitIso`. This is Mathlib's actual inverse-image/extension-of-scalars
  construction, not a new definition of module pullback. It is the canonical adjoint
  comparison target for the explicit `tensorPullback` interface imported by the existing
  algebraic-equivalence module. Mixing their models only inside an isomorphism-invariant
  algebraic-equivalence predicate is harmless; both are the same canonical tensor inverse
  image. No alternate adjunction or comparison is chosen here.

All recorded, available proof-dependency modules are imported without `public`; the
unrecorded proof inputs `lem-sfb-projective-picard-identity-representability`,
`lem-sfb-abelian-closed-subgroup-reduced-component`, `lem-sfb-abelian-structure-h1-dimension`
and `lem-sfb-closed-translation-stabilizer` have no usable Lean record and are not needed
to type this statement. Their full natural-language use remains in its proof docstring.
No prerequisite statement was replaced by a stronger assumption.

Searches (raw remote-search summary is in the sandbox searches.jsonl):

* LeanFinder: "Dual abelian variety represents rigidified algebraically trivial line bundles
  Poincare polarization homomorphism". Eight unrelated hits (root-system polarization,
  ring Picard duality, character modules); no exact result or representing datum.
* Loogle: "AlgebraicGeometry.IsAbelianVariety, AlgebraicGeometry.IsIsogeny". Zero hits,
  unknown Mathlib identifier IsAbelianVariety (it lives in the upstream project).
* Mathlib grep: "Poincare|DualAbelian|polarization|Picard", AlgebraicGeometry.
  Three Weierstrass comments about ring Picard groups, no dual abelian variety.
* LeanSearch: "Poincare sheaf representing rigidified algebraically trivial line bundles
  on an abelian variety". Eight hits about ring relative Picard groups, sheaves and
  abelian sheaf categories, none giving this statement.
* Local rg on WeilConjectures and Sheaf for Poincare, DualAbelian, AlgebraicallyTrivial,
  algebraicEquiv and rigidified families, plus item-id grep in WeilConjectures: no exact
  statement or Poincare datum; the landed `LineAlgebraicEquivalence` notion is reused.
  `RigidifiedLines` is an algebraic-space groupoid, not a scheme Poincare representing datum.
  `Picard/Jacobian` was read: its `IsPicardZeroMul` and Picard subfunctor use fibrewise
  degree zero for curves, not algebraic equivalence on arbitrary abelian varieties.
* DAG rg for the same concepts and `tools/blueprint_refs.py search 'dual abelian'`
  found no definition node for this datum (blueprint search zero matches).
  `tools/blueprint_refs.py ancestor` reports None, consistent with the inherited broken
  ancestor chain; the new node retains the item's from.place and prepends its id to via.

Source read: local Milne AV PDF, printed pp.34–41, including Prop.8.1/Rem.8.2,
Prop.8.4/Rem.8.5, the universal property and Rem.8.7, the normalized difference
construction, its explicit extension to any scheme T on p.40, and §9's opening.
The current blueprint unit `_section.md` was read; this item is an auxiliary, not that
unit's own statement. No statement correction or STATEMENT-DISPUTED issue was found.

Edge cases checked before writing:

* Dimension zero, including A = Spec k: no positive dimension assumption is present.
* L trivial, and F = 0 / unit ideal: the zero homomorphism is an isogeny exactly when
  A has dimension zero; the trivial line is ample exactly in that same case.
* Algebraically trivial L has zero classifying homomorphism; no ampleness is assumed
  for the homomorphism construction, translation or pullback formulas.
* Positive characteristic and nonreduced finite kernels: there is no separability or
  etaleness assumption; `IsIsogeny` retains scheme-theoretic finiteness.
* Empty T: the universal property still quantifies over it. Nonreduced and non-finite-type
  T are admitted. Fibrewise triviality is tested after geometric extension, not merely on
  k-points. Universes are bound explicitly; Ω is in the same universe as k and schemes,
  so there is no independently smaller test universe producing vacuous hypotheses.
* a can be zero, the identity, an isogeny, or an arbitrary abelian homomorphism;
  E can be any normalized representing datum. No arbitrary choice of dual of B is fixed.

Validation: both delivered files compiled individually through the prescribed scompile.py
in dependency order; a final pass after the last definition edit and the delivery checks
are recorded below.

## New nodes

`def-sfb-abelian-dual-poincare-datum` defines the normalized representing datum,
its identity-axis pullback, geometric-fibre algebraic triviality, the normalized difference
family and its classifying condition. Source: Milne AV I §8 pp.36–40 and §9 opening.
The searches above found no existing datum; the constituent notions are reused.
Every construction has real data. The comparison's equality is assembled from existing
cartesian-product and category laws, not a new postponed well-definedness theorem.
The group law, universal property and geometric-fibre requirements are structure fields,
not unproved assumptions added to the item: the item asserts existence of the whole datum.
The new node is in the item's chapter, has the same unit, carries its own module and
lean.declarations, and is cited from the item. The existing landed
`def-sc-isogeny` is also added to stmt_deps because the final clause uses that exact notion.

## Second reading by Q144

I reread the node and both final files clause by clause; this is an explicit self-reading,
not a claim of an independent agent review (the dispatch forbids starting other agents).
The hypotheses match the algebraically closed base and the upstream abelian variety.
The datum includes every scheme parameter, every rigidification, geometric rather than
rational fibres, uniqueness on isomorphism classes, both axes, and the tensor group law.
The dimension equality, normalized family, point formula, translation, general pullback,
inversion, and effective Cartier equivalence are each matched above to a separate clause.
The translated family initially used an unavailable `GrpObj.mulLeft` name; I replaced it
by its actual cartesian lift followed by the given group law. The datum initially left
its group law unrelated to tensor product; I added `tensorGroupLaw`. The pullback
comparison initially contained a small tactic proof of its naturality equality; I replaced
it by a composite of already proved cartesian and category laws so that every new theorem
still has exactly `sorry` as its proof. No mathematical hypothesis or conclusion was
changed. `pullbackComp` orientation and group unit/multiplication projections were checked
against their source signatures and corrected during compilation. The independent
maintainer review remains the delivery's independent check.

Final validation: the final sources compiled separately through scompile.py with no
errors or warnings (only the permitted postponed theorem). The first delivery dry run
requested the current schema's `import_flags` field on the new definition node; I added
the empty list and reran the prescribed wrapper. No source or statement changed.
