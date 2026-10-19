## Worker report

The module `Sheaf.Paper.ProjectionFormulaProperPiece` states
`AlgebraicGeometry.Scheme.proEtaleProjectionFormula_properPiece`, with `sorry`
as its proof. The mathematical statement and proof plan are unchanged. Every
postponed theorem remains named and documented; all definitions contain actual data.

Hypothesis and clause correspondence:

- `{X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f)` supplies the chosen
  factorization X --j--> Z --p--> Y, with j = d.i, p = d.g, Z = d.Z and
  f = j ≫ p from d.comm. The structure supplies properness of p and open
  immersion of j. `[QuasiCompact d.i]` supplies the source's quasi-compactness,
  which upstream Compactification does not require.
- `RY`, `RZ`, `RX` are the coefficient ring sheaves on the original small
  pro-etale sites. `cp`, `cj` identify their inverse images, expressing the
  induced coefficient systems. Site objects have universe u+1, morphisms u,
  coefficients and modules u+1; no equality of site universes is imposed.
- `a`, `b : ProEtaleTensorModel ...` present derived tensor, characterized on
  flat K-flat representatives by the canonical signed tensor total. They are
  presentation choices for the specified operation.
- `E : DerivedCategory (proEtaleRingModules X RX)` is unrestricted and unbounded.
  `(proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E` is A = j_!E.
  `K`, `hK`, `rep` choose the K-injective representative of A required for rho.
  Every A admits these data by `DerivedCategory.exists_iso_Q_obj_of_isKInjective`;
  they impose no boundedness or finiteness condition on E.
- `F : CochainComplex (proEtaleRingModules Y RY) ℤ` and `hb` express the bounded
  coefficient complex: its terms vanish outside a finite integer interval.
  `P : SheafOfModules.StrictPerfectCoefficientPackageOnSite ... F` supplies
  `N : ℤ → ℕ`, inclusion i, retraction p, and `i r ≫ p r = 𝟙 (F.X r)`.
  Its coefficient argument is precisely RY forgotten to a ring sheaf. Its
  finite product of unit modules is the finite tuple/free sheaf of the node.
  The degreewise splittings need not commute with differentials.
- `derivedProjectionFormulaMate` with `proEtaleRingDerivedAdjunction` and
  `proEtaleCanonicalTensorComparison` is the specified pi, the adjunct of the
  tensor comparison followed by counit tensor identity.
- Its source is `(Rp_*j_!E) ⊗^L Q(F)`, expressed as `a.tensor.obj` on
  `(proEtaleRingCompactSupportImage d RY RZ RX cp cj).obj E` and Q.obj F.
  This compact-support functor is definitionally j_! followed by Rp_*.
- Its target is `Rp_*(j_!E ⊗^L Lp^*Q(F))`, expressed as derived direct image
  of `b.tensor.obj` on A and the derived pullback of Q.obj F.
- `proEtalePerfectProjectionInverse` is the specified rho: it forms the
  existing `tensorAdjunctionTotalInverse` using P's actual splitting, then
  returns `eB.hom ≫ DerivedCategory.Q.map s ≫ eC.inv`. The comparisons eB
  and eC are canonically normalized on representatives. The recorded
  `tensorAdjunctionTotalInverse_summand` identifies each summand with the
  inclusion / finite-free inverse / retraction formula.
- The first conjunct is pi ≫ rho = identity on the source. The second is
  rho ≫ pi = identity on the target. Thus both invertibility and the specified
  inverse are retained, with diagrammatic composition order.

Dependency declarations used:

- `WeilConjectures.Compactification.Defs`: `AlgebraicGeometry.Compactification`
  and `Compactification.ofIsProper`.
- `Sheaf.Paper.ProjectionCompactification`: `proEtaleRingDerivedOpenExtension`
  and `proEtaleRingCompactSupportImage`, supplied by the dependency repair below.
- `Sheaf.Paper.StrictPerfectPackageOnSite`:
  `SheafOfModules.StrictPerfectCoefficientPackageOnSite`, the already recorded
  package with independent site and coefficient universes. Its full signature,
  docstring and N/i/p/splitting fields were read from the current library.
- `Sheaf.Paper.ProjectionFormulaArrows`: `CategoryTheory.derivedProjectionFormulaMate`,
  `tensorAdjunctionTotalInverse`, `tensorAdjunctionTotalInverse_summand`, and
  `tensorAdjunctionTotal_target_isKInjective`.
- `Sheaf.Paper.ProEtaleProjectionFormulaArrows`: `proEtalePerfectProjectionInverse`
  and its unit / mixed representative interfaces, supplied below.
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`: `ProEtaleTensorModel`,
  `proEtaleOrdinaryTensorPullback`, its naturality, and
  `proEtaleCanonicalTensorComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`:
  `proEtaleRingModuleAdjunction`, `proEtaleRingDerivedAdjunction`, and the actual
  pro-etale module pullback / direct-image operations it imports.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `Functor.rightDerivedFunctorObjQIso` and K-injective representative existence.
- `Sheaf.Paper.ProjectionFormulaTotalization` is a proof-plan import.

Edge cases checked: identity compactification for proper f, empty source and open,
zero E and F, rank-zero finite free terms, arbitrary integer degrees, empty or
all-zero bounded support, splittings incompatible with differentials, unbounded E,
arbitrary characteristic including the zero ring, and arbitrary universe u.

Searches in the original packet: LeanFinder for the proper compactification
projection formula found unrelated compactness/limit results; Loogle
`"projection", "tensor"` and Mathlib grep
`projectionFormula|projection_formula|ProjectionFormula` found no match.
LeanSearch returned Internal Server Error; no absence conclusion was drawn.
Direct upstream and side-library rg located the general arrows and tensor
comparison, but no proper-piece theorem; upstream grep of this item's id was empty.
The corresponding blueprint sources (1270 and 1268) were reopened on the server.

Repair searches on 2026-10-16: msearch Loogle `"StrictPerfect"` returned zero hits.
LeanFinder for "Derived projection formula for a proper morphism, bounded finite
projective sheaf coefficients, and the specified counit mate inverse" returned
projective-resolution and condensed internal-projectivity lemmas, no match.
Direct rg for `ProEtaleStrictPerfectPackage|StrictPerfectCoefficientPackageOnSite`
in upstream WeilConjectures and side Sheaf found the landed generalized package in
`StrictPerfectPackageOnSite.lean` and its use in `OpenImmersionTensorPiece.lean`.
The live node records that same generalized package. No new definition is needed.

No mathematical statement correction or disputed statement is required.

## Dependency modules

`def-weil-pbc-projection-compactification`: the recorded
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` concerns etale
sheaves in a fixed abelian coefficient category. It cannot supply j_!E for modules
on these ringed pro-etale sites. `ProjectionCompactification.lean` uses the
existing Compactification, defines extension by zero by its left-adjoint universal
property to actual ringed restriction, states its exactness separately, and defines
its exact derived functor and composite with the actual proper derived direct
image. The adjoint universal property determines the functor up to the unique
adjoint isomorphism; its data are not an arbitrary choice.

`def-weil-pbc-projection-formula-arrows`: the recorded ringed interface equates
site object and morphism universes. `ProEtaleProjectionFormulaArrows.lean`
reexports its general chain constructions and supplies the inverse on the original
small pro-etale sites using the published normalized tensor and adjunction
interfaces. Unit and mixed-tensor comparisons retain their uniqueness equations.
The inverse is localization of the actual specified finite-total map. Helpers
are recorded in lean.declarations and carry source / blueprint / proof docstrings.

## Repair of returned delivery

The returned immutable head failed at both references to
`AlgebraicGeometry.Scheme.ProEtaleStrictPerfectPackage`. The current library
already supplies `SheafOfModules.StrictPerfectCoefficientPackageOnSite` in
`Sheaf.Paper.StrictPerfectPackageOnSite`, with exactly the necessary independent
universes and splitting fields. Both references in the arrows module and the
reference in the proper-piece theorem now use that recorded structure directly,
at the ring sheaf obtained from R or RY by forgetting commutativity.

The arrows module explicitly publicly imports the landed module. The obsolete
sandbox specialization module and its dependency-node override were removed,
so this delivery no longer introduces a second definition of the package or
replaces the landed node record. Only the compactification and arrow dependency
repairs remain. Lean signatures and dates were refreshed. The older report's
second-reading claims are superseded: an independent reader must review this
repair before delivery.

Validation: scompile.py compiled all three delivered modules separately, including
their sandbox and actual library module names, with exit code 0 and no warnings.
The required deliver2.py --no-push is the final packet/preflight check.

## Second reading by Q09

I independently read the item node, all three statement-dependency nodes, the three
sandbox modules, and the declarations they use. The source is a blueprint node,
not a Stacks-tag statement: its referenced Markdown is absent from the local
literature checkout, so I opened the server copies of orders 1270, 1268, 1264,
1263 and their proper-base-change unit. They agree with the DAG's specialization
of the ringed-site signed-totalization argument. No hypothesis concerning a
Noetherian base, a field, characteristic, torsion coefficients, or bounded E
occurs in this source specialization.

Object / hypothesis / conclusion checklist, in the node's order:

1. The chosen factorization X --j--> Z --p--> Y, with f = j followed by p,
   is `{X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f)`.
   I opened upstream `Compactification`: its fields are `Z`, `g`, `i`,
   `comm : f = i ≫ g`, `isProper : IsProper g`, and
   `isOpenImmersion : IsOpenImmersion i`. Thus p = d.g and j = d.i are
   exactly the required arrows. Its open immersion is not necessarily
   quasi-compact; the displayed `[QuasiCompact d.i]` supplies precisely
   the source's missing requirement. Verdict: exact.
2. The coefficient rings on the three ringed pro-etale sites are `RY`, `RZ`,
   `RX`; `cp` and `cj` identify the inverse-image ring sheaves. This is the
   coefficient system induced along the two scheme arrows. I read the
   published `proEtaleRingModulePullback`, canonical module adjunction and
   `proEtaleRingDerivedAdjunction` interface, and the canonical tensor
   comparison's representative equation. They use actual inverse image
   and scalar extension, with the tensor-unit normalization, rather than
   an arbitrary adjunction or comparison isomorphism. Verdict: exact.
3. Derived tensor is presented by `a : ProEtaleTensorModel Y RY` and
   `b : ProEtaleTensorModel d.Z RZ`. Their `representative` natural
   isomorphisms specify localization of the signed ordinary tensor on flat
   K-flat representatives. `proEtaleCanonicalTensorComparison` is uniquely
   normalized by its equation on those representatives. These are
   presentation data for the stated derived tensor, not extra geometric
   assumptions. Verdict: exact.
4. E is arbitrary in the unbounded derived category of modules on X:
   `E : DerivedCategory (proEtaleRingModules X RX)`. The substitution
   A = j_!E is `(proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E`.
   `K`, `hK`, and `rep` supply the representative of this very A used in
   the definition of rho. I opened
   `DerivedCategory.exists_iso_Q_obj_of_isKInjective`: it covers every
   object of an abelian category with K-injective resolutions, without
   boundedness. These are choices available for every A. Verdict: exact.
5. The strict-perfect representative is the actual cochain complex `F`
   on Y. `hb : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)`
   is precisely finite interval support. The landed
   `SheafOfModules.StrictPerfectCoefficientPackageOnSite` has
   `N : ℤ → ℕ`, maps `i r`, `p r` to/from the finite product of unit
   sheaves indexed by `Fin (N r)`, and
   `splitting r : i r ≫ p r = 𝟙 (F.X r)`. Finite tuples are the finite
   free sheaf of the source. The package is on exactly the ring underlying
   RY and imposes no compatibility of the splittings with differentials.
   Bounds are intentionally a separate hypothesis. Verdict: exact.
6. The source of pi is `a.tensor.obj` on `Rp_*(j_!E)` and `Q.obj F`.
   `proEtaleRingCompactSupportImage` unfolds to exact derived extension
   followed by `proEtaleRingDerivedDirectImage d.g RY RZ cp`.
   The target is that same proper derived image applied to
   `b.tensor.obj (j_!E, Lp^*(Q.obj F))`. Verdict: both displayed objects
   agree with the node, including the coefficient categories.
7. The arrow pi is `derivedProjectionFormulaMate` applied to the canonical
   derived adjunction and canonical tensor comparison. I opened its body:
   it is the upstream right-adjoint projection map, with only a bifunctor
   curry/uncurry conversion. It is exactly the adjunct of the tensor
   comparison followed by counit tensor identity. Verdict: exact.
8. The specified rho is `proEtalePerfectProjectionInverse`. Its body uses
   the actual `P.N`, `P.i`, `P.p`, `P.splitting` in
   `tensorAdjunctionTotalInverse`, and defines the derived arrow as
   `eB.hom ≫ DerivedCategory.Q.map s ≫ eC.inv`. I opened the general
   total inverse and its summand statement: precomposition by each
   coprojection gives `V.map (1 tensor L.map i)` followed by the inverse
   finite-free mate and `1 tensor p`. Both differentials retain their
   signed-total convention. The mixed-tensor comparisons in this packet
   have unique resolution normalization; the K-injective comparison is
   upstream `rightDerivedFunctorObjQIso`. Verdict: this is the specified
   finite-total inverse, not merely an unspecified inverse.
9. The first conclusion is pi followed by rho equal to the identity of
   `(Rp_*j_!E) tensor^L F`; the second is rho followed by pi equal to the
   identity of `Rp_*(j_!E tensor^L Lp^*F)`. These two equations express
   the displayed isomorphism with precisely its named inverse. Objects,
   order of composition, and quantifiers all agree. Verdict: exact.

Dependency-module reading (H13):

- `def-weil-pbc-projection-compactification`: I opened the recorded
  `Etale.rightDerivedLowerShriekOfCompactification`; it acts on ordinary
  etale sheaves with a fixed coefficient category, not these ringed
  pro-etale module categories. The replacement reuses upstream
  `Compactification` and its identity compactification. Extension by zero
  is the left adjoint to actual open restriction, and thus is determined
  up to unique adjoint isomorphism. Its named exactness theorem supplies
  the proof data for derived descent. The final definition is literally
  j_! followed by Rp_*. No data are chosen from a bare existence assertion
  without a determining universal property. The dependency repair and
  its `lean.note` are justified.
- `def-weil-pbc-projection-formula-arrows`: the recorded general module's
  ringed-site interface equates site object and Hom universes, so it
  cannot be applied to the original small pro-etale site. This packet
  publicly reexports that module and reuses its general mate, chain mate,
  total inverse and summand characterization; only the original-site
  representative interfaces and resulting inverse are supplied here.
  Unit and mixed comparisons are specified uniquely by normalization
  equations. All postponed helper theorems are named, listed in the
  dependency record and have source/blueprint/proof docstrings. No
  downstream projection-mate theorem is assumed to define these arrows.
- The strict-perfect dependency is already the landed generalized package
  with independent site universes. The packet uses it directly and
  contains no duplicate structure or override of that dependency record.
  There are no new definition nodes to audit under H12.

Edge cases: rank N_r = 0 uses `Fin 0` and the zero finite product; no
positivity is assumed. Zero E, zero F, the empty scheme and empty open,
and an all-zero complex are included. The interval can be empty (b < a)
and its endpoints are arbitrary integers, so negative degrees are retained.
Nonzero terms need only be degreewise retracts; differential-compatible
splittings are not required. E can have nonzero cohomology in arbitrarily
positive and negative degrees. The zero coefficient ring and every
characteristic are allowed. Identity compactification is available for
proper f. The small site's object universe is u+1 and Hom universe u;
coefficients/modules have the stated u+1 size. The generalized package
and the new interfaces preserve these universes, without identifying them
or adding a universe equality. `autoImplicit false` and explicit `universe u`
leave no free variable or universe in the three delivered modules.

Independent searches on 2026-10-16 (actual msearch records appended to
searches.jsonl): LeanFinder, "Derived pushforward commutes with tensoring a
bounded complex of retracts of finite sums of the structure sheaf, with
inverse from split projective terms", returned Tor constructions and a
pushforward natural isomorphism, not this statement. Loogle
`"projectionFormula"` returned zero hits. Mathlib grep for
`projection.?formula|tensorAdjunction|extensionByZero` returned only
unrelated connection and Witt-vector references. A second CategoryTheory
grep for projection-formula and extension-zero phrases returned unrelated
triangulated-extension lemmas. LeanSearch for "Projection formula for
derived direct image of sheaves of modules and bounded finite projective
coefficients" returned Internal Server Error: unavailable, no absence
verdict drawn. Direct rg in upstream WeilConjectures, its pro-etale
framework, the upstream name index, and side Sheaf located the existing
mates and general totalization, but no theorem for this proper-piece
statement or general-ring extension API. I also opened
`sfIntrinsicExtensionByZero`, its exactness theorem, and the localized
extension adjunction: those require finite constant coefficient rings,
so they cannot replace the arbitrary ring-sheaf interface of this item.

Mismatches and changes: no mathematical mismatch remains in the repaired
worker packet. The obsolete package references described in its repair
history are absent. I did not rewrite correct Lean or DAG statements.
My change is this independent clause-by-clause, dependency, canonical-map,
universe, edge-case and search audit. The node has no `statement_change`;
no source correction or citer audit is required. All signatures match
`lean.statement` verbatim after whitespace normalization, and no Lean
line exceeds 100 characters. All six postponed theorems have `sorry`
proofs; the remaining declarations supply actual constructions or extract
proof data from named theorems.

Second-reader validation: the prescribed scompile.py invocation compiled all
three delivered files, including preliminary dependency builds and each sandbox
and library-name check, with exit code 0 and no warnings or errors. The wrapper
retained its default per-file limits; no global build or direct live-library
compilation was run.
