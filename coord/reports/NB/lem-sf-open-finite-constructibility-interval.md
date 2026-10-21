## Worker report

The module `Sheaf.Paper.OpenFiniteConstructibilityInterval` states
`AlgebraicGeometry.Scheme.open_finite_constructibility_interval`, with one `sorry`
and no new definitions. It uses ordinary intrinsic constant-ring modules on the small
pro-etale sites, not a completion or a restricted derived category.

The natural-language statement is unchanged. Added statement dependencies are already
landed nodes whose interfaces occur in the signature: `def-weil-extension-by-zero`,
`def-constructible-stratification`,
`def-weil-proetale-geometric-stalk`, and `def-weil-proetale-locally-constant-sheaf`.
No new node and no dependency repair are needed.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `l : ℕ`, `[Fact l.Prime]` |
| Finite extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]` |
| Valuation ring, chosen uniformizer, P_n=A/t^n | `Padic.coefficientExtensionRing l E n`, the recorded quotient of `coefficientExtensionIntegers` by `coefficientExtensionIdeal`, using the recorded chosen uniformizer |
| n >= 1 | `n : ℕ`, `hn : 1 ≤ n` |
| Noetherian V | `[IsNoetherian V]`, exactly locally Noetherian plus quasi-compact |
| Open immersion j:U→V | `{U V : Scheme.{u}}`, `j : U ⟶ V`, `[IsOpenImmersion j]` |
| ell invertible on V | `_hl : ∀ v : V, IsUnit (l : V.presheaf.stalk v)` |
| Small pro-etale sites and constant coefficient rings | `proEtaleDerivedCategory` and `proEtaleRingModules`, with `proEtaleConstantRing`; sites are `Scheme.ProEt`, object universe u+1 and morphism universe u |
| Exact extension by zero and termwise unbounded derived functor | Existing `sfIntrinsicExtensionByZero` and its `Functor.mapDerivedCategory`, with the recorded finite-ring proof and its exactness instances supplied explicitly |
| Integers a <= b | `a b : ℤ`, `_hab : a ≤ b` |
| C in D^b_c(U,P_n) | `_hC : intrinsicFiniteTorsionConstructible l E n hn U C` |
| Input cohomology zero outside [a,b] | `_hC_support : proEtaleCohomologicalSupport C ⊆ Set.Icc a b` |
| Output in D^b_c(V,P_n) | First conjunct, `intrinsicFiniteTorsionConstructible ... V` on the canonical derived extension of C |
| Output vanishing outside the same interval | Second conjunct, cohomological support of that output contained in `Set.Icc a b` |
| H^r(j_!C) is isomorphic to j_!H^r(C), for every r | Third conjunct, `∀ r : ℤ, Nonempty (... ≅ ...)`, with exactly those two homology objects and the recorded sheaf extension functor |
| Any given finite constructible locally closed stratification on U witnessing constructibility of H^r(C) | Universal `r` and `S : FiniteLocallyClosedStratification U`; assumptions `Topology.IsConstructible (S.stratum k)`, `IsLocallyConstantProEtaleModuleSheafOfUniverses` on its pullback, and `Finite (proEtaleGeometricModuleStalk ...)` at every algebraically closed geometric point |
| Reduced closed complement Z | Universal `Z`, `i : Z ⟶ V`, `[IsClosedImmersion i]`, `[IsReduced Z]`, and `Set.range i = (Set.range j)ᶜ` |
| Original strata together with that complement form a constructible locally closed stratification on V | Existential `T : FiniteLocallyClosedStratification V`; constructible images; index equivalence with the retained `Option (Fin S.n)` indices; the `none` immersion is isomorphic over V to i and `some h` to `S.immersion h ≫ j` |
| This output cohomology is locally constant with finite stalks on all extended strata | The last two properties of T, using the same local-constant predicate and all geometric module stalks of the output homology pullback |
| Zero restriction to Z | Final `IsZero (proEtaleConstantModulePullback i ... (H^r(output)))` |
| Empty strata may be omitted | Universal `omitted : Set (Option (Fin S.n))`, with each omitted domain required to be `IsEmpty`; the equivalence e enumerates exactly indices not in omitted. Taking omitted empty retains every original stratum and the complement. Any collection of empty strata, including the empty complement, can instead be removed. |

The `_hl`, `_hab`, and input conditions remain explicit although `sorry` does not use
them. There is no added quasi-compactness hypothesis on j: it follows from the supplied
Noetherian V. There are no field-of-definition, separatedness, finite-type-over-a-field,
étale-origin, or Tor-amplitude assumptions. The derived functor is written directly
using the existing sheaf functor, with no new helper definition.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; the imported
  `Sheaf.NumberTheory.Padics.CoefficientExtension` supplies the recorded quotient ring,
  integer ring, uniformizer, and ideal constructions.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `AlgebraicGeometry.IsNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
  These are proof interfaces for the automatic quasi-compactness of the open.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and
  `ProEt.topology`; `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `CategoryTheory.constantSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`:
  `proEtale_ringed_open_closed`, `proEtaleRingedExtensionByZero` (proof plan).
  Its localized-site extension interface is retained as a proof import. The already
  published intrinsic-coefficient extension is the same sheafified localization
  construction transported by canonical coefficient realization.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory` (the dependency's exact Mathlib match).
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `intrinsicFiniteTorsionConstructible`, the recorded predicate without unused global
  finite-field parameters.
- `Sheaf.Paper.CompletedIntegralCoefficients`:
  `WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0}`, the already proved
  small-site coefficient-universe transport; only this proof interface is used, with
  no completion object or condition in the theorem.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`:
  `proEtaleCohomologicalSupport`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicExtensionByZero`; `ProEtaleIntrinsicExtensionByZeroExact`:
  `sfIntrinsicExtensionByZero_exact` and its three instances.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification` (plus explicit constructibility of strata).
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`:
  `IsLocallyConstantProEtaleModuleSheafOfUniverses`, specialized to the existing common
  scheme/coefficient size; it imposes exactly coverwise constant module models.
- `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`:
  `proEtaleGeometricModuleStalk`.
- Canonical stratum restriction uses `proEtaleConstantModulePullback` from
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, already used by the recorded
  constructibility definition. The other stated proof-dependency modules are imported
  without `public`, including reduced complement, pullback composition, coefficient
  comparison, and exact-functor homology.

Edge cases checked: n=1; arbitrary finite extensions; C=0; any interval including a=b;
U empty; j an isomorphism; V empty; S.n=0 when U is empty; empty original strata;
empty complementary Z. `omitted = ∅` retains all strata, while omitting all empty
strata allows T.n=0 when V is empty. Nonempty geometric fields are quantified in the
scheme's existing size convention. Zero restriction is `IsZero` in the module category,
not `IsZero` on a bare type. No `let` binder or file-local instance/notation occurs.
The explicit `Finite` witness on the sheaf functor is the already proved positive-level
coefficient theorem, not an additional finiteness assumption.

Sources inspected: the complete six-step node proof; Bhatt--Scholze PDF text around
Definition 6.7.6 and Lemma 6.7.7 (preservation of constructibility by the open/proper
factorization); Stacks `proetale.tex`, `lemma-open-immersion` (09BN) and
`lemma-ses-associated-to-open` (09AH), including the quasi-compact open hypothesis.
No source correction or statement dispute was found.

Searches actually run:

- `msearch.py ... leanfinder "Extension by zero preserves finite constructible pro-etale cohomology and cohomological bounds"`:
  eight hits, including affine-limit sections, formally étale products, étale locus,
  `Scheme.etaleTopology`, and `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`;
  none states this node.
- `msearch.py ... loogle '"SheafOfModules", "constructible"'`: zero hits.
- `msearch.py ... grep 'extensionByZero|lowerShriek|constructible' Algebra/Category/ModuleCat`:
  zero hits.
- `msearch.py ... leansearch "Extension by zero preserves constructible sheaves and cohomological bounds"`:
  eight hits on extension of functions, Finsupp, restriction of zero sections, and
  `HomologicalComplex.extendMap_zero`; no match.
- `rg` in `lean/WeilConjectures` for extension by zero and constructibility found
  `Etale.boundedConstructible_mapDerivedCategory_openImmersionLowerShriek` (étale fixed
  coefficients), finite-Tor/proper-open theorems, and condensed module-object results.
  These do not state the present intrinsic finite-torsion theorem on a general
  Noetherian ambient scheme with its universal stratification and interval clauses.
- `grep -rn` for this node id in `lean/WeilConjectures`: no hits.
- `rg` in `lean/Sheaf` found the canonical intrinsic extension and its exactness,
  a finite-stage derived extension helper, and `constantModelConstructible_openImmersionLowerShriek`
  (condensed coefficients over separated finite-type field schemes). Reused the existing
  sheaf functor; none of the found theorem signatures states this node.
- `rg` for `open_finite_constructibility_interval` in Mathlib, `WeilConjectures`,
  `Sheaf`, and `dag/lean_names_upstream.json`: no name collision.

Validation uses the prescribed server `scompile.py` and `deliver2.py --no-push`.
The first version compiled cleanly. The dry run then caught a transitive DAG cycle
through `lem-trf-open-ctf`, whose module owns a convenient finite-stage derived helper.
The repair removes that import and dependency entirely; the final signature spells
out `Functor.mapDerivedCategory` of `sfIntrinsicExtensionByZero` using its existing
exactness instances and the proved positive-level finiteness witness. Thus it
neither depends on the downstream node nor creates a second definition. An imported generic instance
`WeilConjectures.integralCoefficientAbLocallyBijective` has coefficient size
`max u (t+1)` and leaves its first size undetermined in ordinary instance synthesis.
The final signature supplies this existing instance at `{t,u}={u,0}` on U and V,
along with the proved finite-ring witness, by an immediately applied instance lambda.
This is beta-reducible, has no `let`/`have`, adds no hypothesis, defines no new notion,
and declares no file-local instance or notation. All instances are ordinary existing
proof terms. Both actual module categories and the object/morphism site universes stay
unchanged. The repaired complete module compiled cleanly as sandbox (4.6 s) and library
(10.8 s), with no errors or warnings; the final dry run is required before delivery.
Nothing has been proved here.

## Second reading by NB

No independent second worker was started: the dispatcher brief forbids starting agents.
The maintainer performs the independent review under the current direct-delivery procedure.
A final in-thread rereading matched each hypothesis and conclusion against the node as
listed above; it made the optional omission of empty strata explicit instead of merely
retaining them, and checked that direct application of the canonical derived-functor
construction adds no global base or Tor-amplitude assumptions to this theorem.
