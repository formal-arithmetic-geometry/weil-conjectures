## Worker report

The module states the formal-functions comparison for a Noetherian commutative ring `A`, an
`I`-adically complete ideal, a proper morphism `f : X ⟶ Spec A`, a coherent module `F`, and
every degree `p`. It renders the conclusion as a `Nonempty` isomorphism in `ModuleCat` between
`RingedSpace.moduleCohomology X.toRingedSpace p` applied to `F` and the categorical limit of the
cohomology tower of `formalCompletionSystem` for the extended ideal.

The binders `[CommRing A]` and `[IsNoetherianRing A]` render the Noetherian base; `(I : Ideal A)`
and `[IsAdicComplete I A]` render the adic-completeness hypothesis. The scheme and morphism
binders plus `[IsProper f]` render properness. `F : CoherentModules X` renders a coherent
`O_X`-module, and `p : ℕ` renders `p ≥ 0`. The extended ideal is
`(Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f`.
The inverse system is `formalCompletionSystem ... F.obj ⋙
RingedSpace.moduleCohomology X.toRingedSpace p`; its limit is the displayed target.

Dependencies used: `IsNoetherianRing` (Mathlib.RingTheory.Noetherian.Defs), `IsAdicComplete`
(Mathlib.RingTheory.AdicCompletion.Basic), `IsProper` (Mathlib.AlgebraicGeometry.Morphisms.Proper),
`Scheme.IdealSheafData.comap` (Mathlib.AlgebraicGeometry.IdealSheaf.Functorial),
`AlgebraicGeometry.RingedSpace.IsCoherent` (Sheaf.AlgebraicGeometry.Coherent),
`AlgebraicGeometry.formalCompletionSystem` (Sheaf.AlgebraicGeometry.CoherentFormalModule), and
`AlgebraicGeometry.RingedSpace.moduleCohomology` (Sheaf.Topology.RingedSpaceModuleCohomology).

Edge cases checked: `p = 0` is included by `p : ℕ`; `I = ⊥` and `I = ⊤` are allowed ideals;
no nonemptiness assumption on `X` or on the inverse system is introduced. The tower index is
`ℕᵒᵖ` from `formalCompletionSystem`.

Searches: `msearch.py leanfinder` query “theorem on formal functions: cohomology of coherent
sheaf on proper scheme over complete Noetherian ring is inverse limit” found only adic-completion
ring lemmas; `msearch.py loogle`/LeanFinder query “global sections coherent proper inverse limit”
found only unrelated affine-transition limits; grep of Mathlib AlgebraicGeometry and WeilConjectures
for `formal function|FormalFunctions` found no declaration. `rg` over `lean/Sheaf` found no existing
formal-functions statement. Therefore a new declaration was required.

## Second reading by K1

I read the base and sandbox nodes, the Lean module, all seven statement-dependency
records and their declarations. I read coherent.tex on the project server at
5648--5725: Theorem 02OC and Lemma 087U including their proofs. Lemma 087U assumes
exactly a Noetherian complete commutative ring, its ideal, a proper morphism, and a
coherent sheaf, and concludes the comparison for every nonnegative degree.
The sandbox node has no statement_change, no new nodes, and no dependency modules.
No node-statement correction is needed.

Object/hypothesis/conclusion checklist:

- Ring A: `{A : Type u} [CommRing A] [IsNoetherianRing A]`. Verdict: exact;
  Noetherian.Defs defines the last as every ideal finitely generated.
- Ideal and completeness: `(I : Ideal A) [IsAdicComplete I A]`. Verdict: exact;
  AdicCompletion.Basic defines Hausdorff plus precomplete and its
  `AdicCompletion.of_bijective_iff` identifies this with canonical bijectivity.
- Scheme and proper map: `{X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  [IsProper f]`. Verdict: exact; properness includes separatedness, universal
  closedness and local finite type; universal closedness supplies quasi-compactness.
- Extended ideal: `Scheme.IdealSheafData.ofIdealTop` applied to I transported
  by `ΓSpecIso.inv.hom`, followed by `.comap f`. Verdict: exact; ofIdealTop
  generates the ideal on affine opens by restriction of its global generators;
  comap is the ideal of the base-changed closed subscheme, the extended ideal.
- Coherent F: `(F : CoherentModules X)` and `F.obj`. Verdict: exact;
  CoherentFormalModule defines this full subcategory using `RingedSpace.IsCoherent`;
  Coherent defines finite type and finite-type kernels of finite free presentations.
- Cohomology and degree: `(p : ℕ)` and `RingedSpace.moduleCohomology
  X.toRingedSpace p`. Verdict: exact; PQFCohomology explicitly uses the same
  right derived global-sections functors, whose actual signatures I opened.
- Quotient and transitions: `formalCompletionSystem J F.obj`. Verdict: exact;
  its object at `op n` is the cokernel quotient by J^(n+1)F, and its arrows
  are canonical quotient reductions. `formalModuleQuotientπ J (n+1) F.obj`
  is the actual cokernel projection. Positive powers are cofinal in the
  tower containing degree zero, whose zero-power quotient is zero.
- Induced map, compatibility, isomorphism: `∃ e : H ≅ limit ...,
  ∀ n : ℕ, e.hom ≫ limit.π _ (op n) = (moduleCohomology ...).map
  (formalModuleQuotientπ ... (n+1) F.obj)`. Verdict: exact. These equalities
  determine the canonical map uniquely and include compatibility through the
  limit projections. The original `Nonempty (H ≅ limit ...)` omitted this
  crucial clause and allowed an arbitrary isomorphism; I replaced it with
  the displayed existential and projection equations.
- A-linearity: the maps are in ModuleCat over Γ(X,O_X), hence A-linear
  by restriction along f and ΓSpecIso. This adds no strength: the specified
  canonical map is already Γ(X,O_X)-linear, and bijectivity of an A-linear
  map that is Γ(X,O_X)-linear gives a Γ(X,O_X)-linear inverse.
- Degree-zero sections conclusion: p = 0 is included, and the zero right
  derived functor of the left-exact global-sections functor is canonically
  global sections; functoriality identifies the quotient-induced maps.
  The node's 'in particular' clause therefore follows without another hypothesis.

Edge cases: F = 0 and the empty scheme are allowed (all cohomology is zero).
I = 0 gives the constant positive quotient system. I = 1 is covered precisely
when the completeness hypothesis holds, which forces A to be the zero ring.
p = 0 is included; tower index zero denotes power one, not a missing case.
There is no variable index set to assume nonempty; this is the fixed ℕ inverse
system. No characteristic, domain, field, positivity, or nonzero assumptions
are imposed. The universe u is arbitrary, with A and the scheme in the shared
Scheme/Spec universe required by the recorded definitions; smaller objects can
be lifted into a common universe. There is no quantification over test objects
in a smaller universe, and autoImplicit is false.

Independent searches, using msearch.py:

- LeanFinder: 'canonical quotient cohomology inverse limit proper adic complete
  scheme' found affine-transition limits and AdicCompletion algebra maps,
  not formal functions for coherent sheaves.
- Loogle: 'IsAdicComplete' found the completeness class and its ring/module
  lemmas, not sheaf cohomology or the comparison.
- LeanSearch: 'cohomology of coherent module on proper scheme over complete
  Noetherian ring is limit of infinitesimal quotients' was unavailable
  (Internal Server Error); this is not a no-match verdict.
- rg in Mathlib, WeilConjectures and lean/Sheaf using 'formalfunctions',
  'formal_functions', 'formal functions', 'cohomology.*adic' and
  'adic.*cohomology' found unrelated local/ℓ-adic cohomology, monoid algebra
  functions, and FormalSystemsPushPull's proof reference. No declaration
  already states this comparison. The item module itself was excluded.

Repairs: specified the canonical map by all limit projections, added the standard
copyright header, and completed the proof docstring with the four node steps,
the projection identification, positive-power indexing and the p = 0 consequence.
The final module contains one named theorem with proof `sorry`, no new definitions,
no hollow data, and no file-local notation or instance. Its signature is copied
verbatim into lean.statement. The required scompile.py check passed cleanly.
