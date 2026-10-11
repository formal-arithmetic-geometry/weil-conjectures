## Worker report

The main module is `Sheaf.AlgebraicGeometry.CohomologyPowersIdealReesFinite`, declaration
`AlgebraicGeometry.cohomology_powers_ideal_rees_finite`. It states the entire node, with
one named theorem and `sorry`; no proofs or hollow data definitions were written.
The node's statement is unchanged.

Hypotheses and objects, in order:
- Noetherian commutative A: `{A : Type v} [CommRing A] [IsNoetherianRing A]`.
- Ideal I: `(I : Ideal A)`; B is literally `reesAlgebra I`, the Mathlib subalgebra of A[t].
- Scheme and proper map to Spec A: `{X : Scheme.{v}}`, `f : X ⟶ Spec (CommRingCat.of A)`
  and `[IsProper f]`. Universally closed implies quasi-compact, so this is proper in the
  node's finite-type sense.
- Extended ideal: the auxiliary family uses
  `(Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso ...).inv.hom)).comap f`.
  Thus the base ideal is transported to global sections of Spec A and extended by the
  recorded ideal-sheaf comap; no pullback-flatness assumption is made.
- Coherent module F: `(F : X.Modules)` and `hF : RingedSpace.IsCoherent X.toRingedSpace F`.
- Nonnegative q: `(q : ℕ)`, including q = 0.
- I^0 F is literally F with identity inclusion, by `reesModuleSheaf`'s zero equation.
  For n > 0 it is `Scheme.idealModuleProduct` applied to the inclusion of
  `Scheme.idealSheafPower ... n`, with `Scheme.idealModuleProductι` into F.
- M_n: `reesModuleCohomology f I F q n` applies the recorded
  `RingedSpace.moduleCohomology` to that sheaf, then `ModuleCat.restrictScalars` along
  `((Scheme.ΓSpecIso ...).inv ≫ f.appTop).hom`. This is exactly the stated A action.
- The maps lambda are existentially supplied for every k, m and a in I^k. Their first
  conjunct specifies, on EVERY open U and EVERY section s, that their composite with
  the target inclusion is multiplication by `f.appLE ⊤ U le_top` applied to the base
  section a, followed by the source inclusion. They are sheaf-module morphisms, hence
  O_X-linear. Image inclusions are monomorphisms, so this property determines the maps;
  they are not arbitrary extra input hypotheses.

Conclusions:
- (1), module structure: `∃ mod : Module (reesAlgebra I) (⨁ n : ℕ, ... )` supplies the
  module structure on the actual direct sum of the specified cohomology modules.
- The formula specifies its action for every polynomial b in B and every direct-sum
  element x. It sums over `b.val.support` and `x.support`, using `DirectSum.of ... (m+k)`
  of `H^q(lam k m (b.val.coeff k) (b.property k)) (x m)`. The membership proof is the
  actual coefficient condition of B. Since the sum is injected into degree m+k, its
  degree-n component is precisely the node's convolution over k+m=n. The finite-support
  double sum is an equivalent expression for the whole direct-sum vector, including
  coefficients that vanish. This avoids any independently chosen star operation.
- (1), degree zero: the second conjunct explicitly equates `H^q(lam 0 m a ha) x` with
  `a • x` for the A-module defined by restriction of scalars, for all a in I^0 = A.
- (2): `@Module.Finite ... mod` uses exactly the SAME existential module structure as
  the action formula; no unrelated finiteness instance is substituted.

Dependency declarations read and used:
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, all ideals finitely generated.
- `Mathlib.RingTheory.ReesAlgebra`: `reesAlgebra` and its coefficient-membership condition.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`:
  `Scheme.IdealSheafData.comap` for the extended ideal.
- `Sheaf.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: its notation uses the shared
  `Scheme.idealModuleProduct`, `Scheme.idealModuleProductι`, `Scheme.idealSheafPower`
  from `Sheaf.AlgebraicGeometry.IdealModuleProductStalk`; their full definitions were read.
- `Sheaf.Paper.PQFCohomology`: the statement identifies H with
  `RingedSpace.moduleCohomology`, defined in `Sheaf.Topology.RingedSpaceModuleCohomology`;
  the latter actual definition is used (right derived global sections on O_X-modules).
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `toModulesι` supplies
  the genuine ideal inclusion; `Mathlib...IdealSheaf.Basic` supplies `ofIdealTop`.

Edge cases checked mathematically before writing: zero ring and empty scheme are allowed;
F=0 gives the zero direct sum, finite over B. I=0 leaves only degree zero, with the ordinary
finite cohomology module. I=A has I^n F=F and polynomial action shifting degrees, consistent
with a finite A[t]-module. q=0 and m=k=0 are included. Zero b or x has empty support and
acts by the empty sum. No characteristic restrictions or flatness assumptions were added.
All variables and universes are explicitly bound. The same universe for A and X covers
any pair after taking their common maximum; no test objects are quantified in a smaller
universe.

Searches (real calls recorded by msearch.py in searches.jsonl):
- LeanSearch query `cohomology of ideal powers times coherent sheaf finite module over
  Rees algebra`: service unavailable (Internal Server Error), no verdict inferred.
- LeanFinder query `cohomology ideal powers coherent sheaf Rees algebra finite module`:
  eight hits, local ring cohomology and ideal filtrations, none the proper-scheme result.
- Loogle query `reesAlgebra, Module.Finite`: zero hits.
- Mathlib grep `reesAlgebra|idealPowerModule`: ten hits, ReesAlgebra and Filtration,
  only ring/module constructions, no sheaf-cohomology finiteness.
- rg of the source WeilConjectures and project lean/Sheaf for `reesAlgebra`,
  `idealPowerModule`, and the item id: source blowup/Rees grading constructions only;
  no statement matching this node.
- Source checked directly at https://stacks.math.columbia.edu/tag/02O8 (local literature
  files are not materialized on this machine): proper, Noetherian base, coherent sheaf,
  finite graded cohomology module; proof uses 0897 (1), exactly as the DAG proof.

## New nodes

`def-weil-pbc-rees-module-cohomology` packages the graded family and its inclusions,
with degree zero F, and its cohomology as A-modules. Its module
`Sheaf.AlgebraicGeometry.ReesModuleCohomology` defines `reesModuleSheaf` and
`reesModuleCohomology` entirely from the existing products, powers, extension and
cohomology; no new cohomology theory, tensor product or ideal power is defined.
Source: Stacks Section 30.20, paragraph before 02O8. The packaged family is needed to
state all the multiplication maps and the direct sum using the same graded objects.
Existing nodes supply the ingredients but not this packaged family with its specified
zero degree and scalar restriction. `tools/blueprint_refs.py search 'ideal power module'`
found zero blueprint nodes. rg of DAG nodes and Lean sources for the candidate names
found no packaged construction. Searching the DAG for powers cohomology finds the
current result and its related finiteness/application nodes, not a definition of the
packaged family. The node cites all its constituent definition nodes.

Additional searches for this node, recorded by msearch.py:
- LeanSearch `graded family of sheaf cohomology of ideal powers times a module with
  degree zero original module`: unavailable, Internal Server Error.
- Loogle `SheafOfModules, DirectSum`: no hits.
- Mathlib grep `idealPowerModule|idealPowerCohomology|cohomology.*[Rr]ees`: five unrelated
  local, group or nonabelian cohomology hits, no packaged family.
- The same rg query in WeilConjectures and lean/Sheaf found no declaration of this family.

Validation: both delivery modules compiled together on the server, clean, in 2.2 seconds.

## Second reading by J1

I reread the node statement against Stacks Project, Cohomology of Schemes,
Lemma 02O8 and the preceding paragraph (Section 30.20). The objects and their
Lean renderings agree item by item:

- A is `{A : Type v} [CommRing A] [IsNoetherianRing A]`; I is `(I : Ideal A)`;
  B is `reesAlgebra I`, Mathlib's subalgebra of `A[X]` with coefficient
  condition `b.coeff k ∈ I ^ k`.
- X and f are `{X : Scheme.{v}}` and
  `f : X ⟶ Spec (CommRingCat.of A)` with `[IsProper f]`.
- The extended ideal is the comap of
  `IdealSheafData.ofIdealTop (I.map (ΓSpecIso ...).inv.hom)` along f, exactly
  the `reesModuleSheaf` construction. Its degree-zero pair is `⟨F, 𝟙 F⟩`;
  positive degrees use `idealSheafPower`, `idealModuleProduct`, and the recorded
  inclusion into F.
- F and coherence are `(F : X.Modules)` and
  `hF : RingedSpace.IsCoherent X.toRingedSpace F`; q is `(q : ℕ)`.
  `reesModuleCohomology f I F q n` is the stated H^q, restricted along the
  induced A-to-global-sections map.
- The multiplication maps are the existential `lam` family. Its first
  conjunct quantifies k,m,a, a proof `a ∈ I ^ k`, every open U and section s,
  and says that composing with the target inclusion equals multiplication by
  the image of a followed by the source inclusion. This is the node's
  `lambda` condition on every open.
- The conclusion's module structure is the existential `mod` on
  `⨁ n, reesModuleCohomology ... n`; the displayed `SMul.smul` equality sums
  over the finite polynomial and direct-sum supports and inserts each term in
  degree `m + k`, which is equivalent to the node's convolution formula.
  The next conjunct is the degree-zero equation, and
  `@Module.Finite ... mod` is finiteness for that same structure.

No mismatch was found and no Lean or node statement was changed. Edge cases
remain covered: q = 0, n = 0 (where the family is literally F), I = 0 and
I = ⊤, zero F, zero b or x (empty supports), the zero ring, and empty schemes;
there is no characteristic, flatness, or extra finiteness hypothesis. Both
modules compile together with only the theorem's permitted `sorry`.

I repeated the existing-definition searches (LeanSearch, LeanFinder/Loogle,
grep of Mathlib, WeilConjectures, and `lean/Sheaf`) for Rees cohomology and the
graded ideal-power family. They found only ring-level `reesAlgebra` and
unrelated cohomology; no declaration duplicates either delivered notion.
