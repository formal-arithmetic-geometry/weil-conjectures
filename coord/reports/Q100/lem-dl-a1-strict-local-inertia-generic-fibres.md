## Worker report

Module: `Sheaf.AlgebraicGeometry.StrictLocalInertiaGenericFibres`.
Declaration: `AlgebraicGeometry.Scheme.strictLocalInertiaGenericFibres`.
This is one theorem with proof `sorry`; it states all clauses of the node. No definition,
new node, dependency repair, or statement correction is needed. The node is unchanged
except for `lean`. Sources read: Stacks `pione.tex`, the setup and first proof paragraph
of 0BTD, the setup and proof of 0BSW, and the trivial-composition paragraph of 0BSM.
Also read the current blueprint's `rem-dl-a1-conventions.md`, second paragraph, in
`literature/blueprint/latest/`: this lemma provides the general normal-scheme input to
its inertia criterion, rather than restricting to the affine line.

Hypotheses and clauses, matched individually:

- Integral X: `(X : Scheme.{u}) [IsIntegral X]`. Mathlib's definition supplies nonemptiness
  and domain sections on every nonempty open. Normality is
  `hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)`; each stalk is already a
  domain by Mathlib's integral-scheme instance. Together these are exactly the node's
  normal-domain local rings, without a Noetherian assumption.
- K is the generic stalk: `X.functionField`, defined by Mathlib as precisely that stalk,
  with its field structure for an integral scheme. The generic structural map is
  `X.fromSpecFunctionField`, the upstream abbreviation for `X.fromSpecStalk (genericPoint X)`.
- Chosen separable closure: `(Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
  [IsSepClosure X.functionField Ω]`. `IsSepClosure` means separably closed and separable
  over K; separability entails algebraicity. G is always `Ω ≃ₐ[X.functionField] Ω`.
- The choice at x is encoded by an arbitrary geometric point
  `{Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ] (s : Spec (.of Ξ) ⟶ X)`.
  Its underlying point is `x = s (default : Spec (.of Ξ))`; a field spectrum has exactly
  one point. Thus this quantifies over all points and their chosen geometric points,
  including nonclosed points. Every point admits such a choice by taking an algebraic
  closure of its residue field. This uses the precise geometric-point interface of
  the recorded strict-henselization dependency, not a perfectness assumption on κ(x).
- The prescribed strict henselization is `strictHenselizationRing s`; its scheme and
  structural map are `strictHenselizationScheme s` and
  `strictHenselizationStructuralMap s`, all from the dependency modules.
- Domain: the first existential witness is `IsDomain (strictHenselizationRing s)`.
  This is a conclusion, not a hypothesis. The following fraction ring therefore has
  the actual fraction-field structure.
- The canonical K-structure on this fraction field is the ring homomorphism `k`.
  The first conjunct explicitly requires its spectral composite with the generic
  structural morphism to equal the composite of `Spec` of the fraction inclusion
  with `strictHenselizationStructuralMap s`. This is exactly compatibility with the
  structural map. It is not an arbitrary field map: the displayed equation determines
  the generic lift, equivalently the extension of the structural stalk map to fractions.
- Existence of compatible embedding: `∃ i, i.comp k = algebraMap X.functionField Ω`.
  Homomorphisms from the fraction field to the field Ω are automatically injective.
  Using ring homomorphisms with this equation avoids imposing or choosing an additional
  K-algebra instance on the fraction field.
- J for any embedding i is the existing
  `fixingSubgroup (Ω ≃ₐ[X.functionField] Ω) (Set.range i)`.
  Its membership says exactly `∀ z, g (i z) = i z`.
- Any two compatible embeddings: the second block quantifies over both i,j with their
  compatibility equations and gives `g : Ω ≃ₐ[X.functionField] Ω` with
  `∀ z, j z = g (i z)`.
- Conjugacy with the same g: the next clause says for every h that
  `h ∈ J_j ↔ g⁻¹ * h * g ∈ J_i`. This is exactly `J_j = g J_i g⁻¹`, expressed by
  membership to avoid introducing a separate conjugate-subgroup construction.
- Every finite étale cover P: `∀ P : X.FiniteEtale`. Its base change is
  `pullback P.obj.hom (strictHenselizationStructuralMap s)`, with projection
  `pullback.snd`. The splitting is an isomorphism in `Over` the strict-local scheme
  to `Over.mk (Sigma.desc (fun _ : Fin n ↦ 𝟙 (strictHenselizationScheme s)))` for
  `∃ n : ℕ`. Thus it is a finite disjoint union over the base, not just an abstract
  scheme isomorphism or a collection of points. In particular n = 0 is permitted.
- Trivial action: for every compatible i, every P, every `g ∈ J_i`, and every
  `t : Spec (.of Ω) ⟶ P.obj.left` whose composite to X is the fixed generic geometric
  point, the theorem says `Spec.map (CommRingCat.ofHom g.toRingHom) ≫ t = t`.
  By the fibre-product universal property these are exactly the elements of
  `Hom_K(Spec Ω, P_K)`. Precomposition with Spec g is the standard G-action on this
  set (using inverses gives the same triviality assertion). No surjectivity or
  connectedness of P is assumed.
- Nonempty affine opens: the last block quantifies over `(U : X.Opens) [Nonempty U]
  (hU : IsAffineOpen U)` and states `IsDomain Γ(X,U)`, `IsIntegrallyClosed Γ(X,U)`,
  and `IsFractionRing Γ(X,U) X.functionField`. The fraction-field algebra is the
  existing germ-to-function-field algebra.
- Integral closure: `integralClosure Γ(X,U) Ω`, whose carrier is exactly the elements
  integral over Γ(X,U). The block quantifies over its compatible algebra instance
  `[Algebra Γ(X,U) Ω] [IsScalarTower Γ(X,U) X.functionField Ω]`.
  This introduces no extra hypothesis on X or Ω: such a structure is the composite
  of the germ map with K → Ω, and the tower condition forces exactly that composite.
  The claim holds for every presentation of this canonical structure.
- Prime lying over x: `r : PrimeSpectrum (integralClosure Γ(X,U) Ω)`, with the equation
  `(Spec.map (CommRingCat.ofHom (algebraMap Γ(X,U) (integralClosure Γ(X,U) Ω))) ≫
    hU.fromSpec) r = s default`. This is precisely contraction followed by the affine
  chart into X, so it neither assumes x closed nor assumes r maximal.
- Inertia: `r.asIdeal.inertia (Ω ≃ₐ[X.functionField] Ω)`. Mathlib's integral-closure
  action is the restriction of each K-automorphism of Ω. The definition says
  `∀ c : C, g • c - c ∈ r`. For a group of ring automorphisms this implies stability
  of r (apply the same condition to g and g⁻¹), and is equivalent to triviality on
  C/r, hence on Frac(C/r). This is precisely the node's decomposition-and-residue
  inertia group; a second definition would duplicate an existing notion.
- Finally, for every compatible i there is g such that for every h,
  `h ∈ r.asIdeal.inertia G ↔ g⁻¹ * h * g ∈ J_i`. This is exactly conjugacy of the
  affine normalization inertia group with the chosen J_x.
- No Noetherian, finite-dimensional-extension, perfect-field, characteristic,
  closed-point, or nonempty-cover hypothesis occurs. All universes and variables
  are explicitly bound; `set_option autoImplicit false` is included.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral` (docstring and
  fields), through `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, read as
  `IsIntegrallyClosedIn R (FractionRing R)`. The domain component is Mathlib `IsDomain`;
  the stalk domain instance is in `Mathlib.AlgebraicGeometry.FunctionField`.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem`, with its full signature/docstring read;
  the actual separable-closure structure is Mathlib's `IsSepClosure`, reexported there.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `AlgebraicGeometry.Scheme.strictHenselizationRing`,
  `strictHenselizationScheme`, and the representative-category construction.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `AlgebraicGeometry.Scheme.strictHenselizationStructuralMap` and its characterization
  `exists_strictHenselizationStructuralMap`, with signatures and docstrings read.
- `WeilConjectures.AlgebraicGeometry.GaloisCategories`: `Scheme.FLC` is the record's
  principal declaration; its documentation explicitly identifies the already supplied
  `Scheme.FiniteEtale` and `Scheme.FiniteEtale.fiber` in
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`. Those declarations'
  full signatures/docstrings were read; this theorem uses `Scheme.FiniteEtale`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, its carrier
  and algebra-map fields, and its `MulSemiringAction` instance.

Public imports expose the definitions used in the signature. All recorded proof-dependency
modules with Lean records are imported privately unless already public. The remaining
proof dependencies have only Mathlib matches, already available for the indicated proof
steps. The ten-step natural-language proof is in the theorem docstring. In particular
`Sheaf.RingTheory.HenselianGlobalInertiaComparison` was read in full: it supplies the
local comparison, not this full global scheme statement.

Edge cases checked before writing:

- Integral X excludes the empty scheme, exactly as the node does. Empty P is allowed
  with n = 0, and the action on its empty fibre is vacuously trivial.
- A generic point or any nonclosed point can be the image of s; r is only prime.
  The relevant residue field is Frac(C/r), not C/r assumed to be a field.
- An imperfect field is allowed. Ξ is an algebraically closed field specifying a
  geometric point; Ω is only a separable closure of K. They are different fields.
- Infinite strict-local fraction extensions and infinite Ω/K are allowed; there is
  no finite-dimensionality hypothesis. Embedding conjugacy uses normal algebraic
  extension, not an argument restricted to finite extensions.
- A strictly henselian X or X = Spec K does not force a nontrivial J: the corresponding
  trivial fixing group and zero-degree splitting cases remain included.
- Affine opens must be nonempty to have fraction field K; no empty open is quantified.

Searches performed (the wrapper records their actual output in searches.jsonl):

- `msearch.py leanfinder`: "Strict henselization fraction field of normal integral scheme
  embeds into separable closure and its fixing subgroup equals normalization inertia".
  Eight hits, including `ValuationSubring.inertiaSubgroup`,
  `IsGaloisGroup.iff_isFractionRing`, `IntermediateField.map_fixingSubgroup`,
  `IsGaloisGroup.of_isFractionRing`, `Ring.instIsGaloisFractionRingNormalClosure`,
  `IsGaloisGroup.to_isFractionRing`, `galLift`, and
  `FiniteGaloisIntermediateField.mem_fixingSubgroup_iff`. None is the scheme statement.
- `msearch.py loogle`: `IsSepClosure, IntermediateField.fixingSubgroup`: zero hits.
- `msearch.py grep`: `strictHensel|strict_hensel|inertiaSubgroup`: one hit,
  `ValuationSubring.inertiaSubgroup` in Mathlib/RingTheory/Valuation/RamificationGroup.lean;
  this concerns valuation subrings, not arbitrary normal local rings or finite étale covers.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, for inertia, strict-henselization
  fraction fields, and the exact node id: the full theorem has no existing declaration.
  Found and read the local comparison module and upstream finite-étale/inertia modules;
  neither contains all clauses here. Search in `dag/lean_names_upstream.json` likewise
  found finite-étale splitting declarations but no declaration for this node.
- Direct Mathlib searches/readings found and reused `fixingSubgroup` in
  GroupTheory/GroupAction/FixingSubgroup.lean and `Ideal.inertia` in
  RingTheory/Ideal/Defs.lean instead of defining private variants.

Validation: prescribed `scompile.py` passed for the exact delivered module, both its
sandbox and library paths, without errors or warnings. All postponed work is the one
named theorem and its `sorry`; no data is postponed.

## Second reading by Q100

Single-worker rereading: the dispatcher explicitly forbids starting other agents.
This section records my separate read of the completed file against the node; it does
not claim an independent worker review. The maintainer performs the independent review
of the delivery under this dispatch's instructions.

I reread the entire signature and the dependency interfaces. The domain witness occurs
before any fraction field, so domain-ness is proved as a conclusion. The map k is constrained
by an equality of actual scheme morphisms; embedding compatibility is tested on K, not
just on the ring of an arbitrary chart. The same conjugating element satisfies j = g i
and the subgroup relation, with the direction `g⁻¹ h g ∈ J_i`. The splitting is over the
strict-local base and permits Fin 0. The action fixes actual Ω-valued generic lifts, not
just the underlying topological points. The affine conclusion uses the canonical germ
algebra, and every compatible presentation of its composite to Ω is covered. The lying-over
condition uses Spec of the inclusion, and the inertia comparison is for primes, not only
maximal ideals. I checked that `Ideal.inertia` already enforces the stipulated prime
stability as well as the identity residue action. No clause is omitted, no extra
mathematical hypothesis is imposed, and no node correction was necessary.
