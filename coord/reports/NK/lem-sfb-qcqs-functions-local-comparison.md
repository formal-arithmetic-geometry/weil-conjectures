## Worker report

Module: `Sheaf.AlgebraicGeometry.QcqsFunctionsLocalComparison`. Main declaration:
`AlgebraicGeometry.qcqs_functions_local_comparison`. It states the entire node in one
conjunction, with `sorry` as the sole theorem proof. Seven auxiliary definitions construct
only the canonical objects and maps occurring in this node; all their data are explicit.
There are no new nodes, dependency repairs, or statement changes.

Hypothesis and clause correspondence:

- Schemes and morphism: `{Y T : Scheme.{u}} (f : Y ⟶ T)`. Quasi-compactness and
  quasi-separatedness: `[QuasiCompact f] [QuasiSeparated f]`. There is no finite-type,
  affine-source, separated, Noetherian, reduced, nonempty, or nontrivial-ring assumption.
- Canonical sheaf map beta: `f.c`. Its component is `f.app U`, and its stalk component
  is `(TopCat.Presheaf.stalkFunctor CommRingCat y).map f.c`. The target presheaf is
  `qcqsFunctionsPushforward f`, the actual Mathlib direct image of `Y.presheaf`.
- Affine open V: `(V : T.Opens) (hV : IsAffineOpen V)`. R is exactly `Γ(T,V)` and M
  exactly `Γ(Y,f ⁻¹ᵁ V)`. The structural R-to-M ring map is `(f.app V).hom`.
  `qcqsFunctionsChart f V` is the restriction of f followed by `V.toSpecΓ`, hence is
  the structural morphism `Y_V → Spec R`. Affineness identifies V with Spec R.
- A multiplicative subset is `S : Submonoid Γ(T,V)`, including sets containing zero.
  `qcqsFunctionsLocalization f V S` is `Localization (S.map (f.app V).hom)`. This is
  ordinary ring localization at the image of S, rather than localization at a prime
  of M: M need not have a prime over the chosen prime of R. The ring Localization
  API is used for the multiplicative structure; its fractions have precisely the
  module-localization relation `u(tm-sn)=0` stated in the dependency. It is not a new
  quotient or a private replacement for Mathlib's localization.
- The base localization is expressed in any presentation `(B : CommRingCat.{u})`,
  `(φ : R →+* B)`, `hB : @IsLocalization R _ S B _ φ.toAlgebra`. In particular take
  B to be `Localization S` and φ the algebra map to recover the literal S⁻¹R of the
  node. This also accepts `B = O_{T,y}`, and any iterated-localization presentation,
  without imposing a new ring identification or choosing an arbitrary coefficient map.
- `qcqsFunctionsBaseChange` is the Mathlib `pullback` of the chart morphism and
  `Spec.map (CommRingCat.ofHom φ)`. It is `Y_V ×_V Spec B` after the canonical
  affine identification. `qcqsFunctionsNumerator` is pullback by its first projection,
  composed with `(f ⁻¹ᵁ V).topIso.inv` to identify the open's two section presentations.
  `qcqsFunctionsCoefficient` is pullback by the second projection, composed with the
  canonical `Scheme.ΓSpecIso B` identification. These are fully constructed maps.
- The family θ consists of ring equivalences. The first equation is
  `θ(m/s) * coefficient(φ(s)) = numerator(m)`. Since φ(s) is a unit by hB, this
  specifies exactly `θ(m/s) = (1/s) pr₁♯(m)` and fixes θ on every fraction.
- The second equation, with numerator `f.app V a`, gives `θ(a/s)=coefficient(a/s)`.
  Thus θ is an S⁻¹R-algebra isomorphism, expressed as a ring equivalence with its
  full coefficient normalization rather than installing local Algebra instances.
  Every b in B is a fraction, so the equation covers all structural coefficients.
- Further localization is the third conjunct: for the compatible coefficient ring map
  t, the map q has exactly the two pullback-projection equations, and l has exactly
  the numerator equation. These conditions uniquely determine the canonical maps by
  the pullback and localization universal properties. The conclusion is the commuting
  square `θ' (l z) = q.appTop (θ z)` for every z. Quantification over normalized maps
  expresses functoriality without choosing another construction. The standard maps
  exist by Mathlib `pullback.lift` and `IsLocalization.map/lift`. It includes S ≤ S'
  and successive localizations: an iterated localization is again a localization of R
  at the preimage of the second denominator set, so it is among these B,C presentations.
- For y in V, `hV.primeIdealOf y` is the exact corresponding prime of R, and
  `(hV.primeIdealOf y).asIdeal.primeCompl` is its complement. The equivalence e runs
  `M_p ≃+* F_y`; the requested first isomorphism is `e.symm`. Its denominator-clearing
  germ equation fixes it as `m/s ↦ m_y / beta_y(s_y)`.
- The next equation explicitly specifies the inverse on germs. For any neighborhood
  `W → V`, a section z satisfying `m|_W = s|_W z` has
  `e.symm (germ_W z) = m/s`. Taking W = D(h), s = h^n, gives verbatim the requested
  rule for the germ of `m/h^n`. Using any neighborhood for the same equation records
  independence of the representative, without assuming M has no zero divisors.
- A is the actual local ring `T.presheaf.stalk y`. `hV.isLocalization_stalk y`
  supplies precisely the germ-map localization presentation of `R_p = A`, from the
  recorded affine-open-stalk Mathlib dependency. θ at this presentation is the second
  isomorphism. The final equation of the first conjunct is
  `θ (e.symm (beta_y a)) = coefficient a` for every a in A. This fixes the A-algebra
  structures on both comparisons and identifies the stalk of beta with the coefficient
  map. The composite on a general germ is its pullback: represent the germ on D(h),
  use the displayed e.symm formula, then the θ fraction formula with that same h^n.
- The next main conjunct states `IsIso f.c ↔ ∀ V hV y, Function.Bijective coefficient`.
  Bijectivity is isomorphism for rings. Every point has an affine neighborhood, so this
  is exactly the all-points criterion, with the same local base changes just compared.
- Finally, invertibility gives a family `σ U : Γ(Y,f⁻¹U) ≃+* Γ(T,U)` on every open U.
  Both inverse equations against `f.app U` are stated. The last equation says σ
  commutes with restriction along every `i : W ⟶ U`. The criterion immediately gives
  this conclusion when all coefficient maps are invertible, as in the node.

The theorem docstring reproduces all ten proof steps and names their DAG inputs.
All helpers have the item's source and blueprint tag. No theorem besides the main one
is postponed and no definition takes data from an existence assertion with sorry.

Dependency declarations used, read with signatures and docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`, `Scheme.ΓSpecIso`, `Scheme.Hom.app` and `appTop`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: the recorded module, whose
  quasi-compact clause is `AlgebraicGeometry.QuasiCompact` (declared in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`). No `LocallyOfFiniteType` premise.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`, defined by
  quasi-compactness of the diagonal; the permanence and affine-base facts in proof steps 1.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: recorded `LocallyRingedSpace.Hom`,
  inheriting the canonical sharp natural transformation from `PresheafedSpace.Hom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`; the actual universal fibre product, not an abstract replacement.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` is localization
  at `primeCompl`. The same Localization fraction construction is used above.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: recorded `LocalizedModule` fraction
  relation and module localization; for the ring-valued specialization we use Mathlib's
  ring `Localization` as explained above, with the image submonoid in M.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`: recorded
  `PresheafOfModules.moduleStalkFunctor`, `stalkObj`, `stalkMap` reuse Mathlib stalks.
  Here the sections and germs are ring-valued, so their direct ring form is
  `TopCat.Presheaf.stalk`, `germ`, `stalkFunctor`, from `Mathlib.Topology.Sheaves.Stalks`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen.primeIdealOf`,
  `isLocalization_stalk`, `fromSpec_app_self`, and basic-open localizations.
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.topIso`, `morphismRestrict`,
  `isPullback_morphismRestrict`.
- Proof imports also include `Mathlib.AlgebraicGeometry.Morphisms.Flat`
  (`Flat.SpecMap_iff`, `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`),
  `Mathlib.RingTheory.Flat.Localization` (`IsLocalization.flat`),
  `Mathlib.RingTheory.Localization.BaseChange` (`IsLocalization.tensor`),
  `Mathlib.AlgebraicGeometry.ResidueField` (affine section vanishing),
  `Mathlib.RingTheory.Spectrum.Prime.Topology` (principal-open basis), and
  `Mathlib.Topology.Sheaves.Stalks` (`isIso_iff_stalkFunctor_map_iso`).

Edge cases checked mathematically: S = {1}; 0 in S (both localized source and base-change
section ring are the zero ring); the empty Y; an empty affine V; the empty T (the
all-points condition is vacuous and the unique empty-space sheaf map is invertible);
f = identity; noninjective R → M; zero divisors; primes with empty inverse image;
localizing Z → Z[1/2] at (2), where M_p can be Q, not zero. No assertion identifies M_p
with the fibre ring M tensor κ(p). All universes are explicitly bound, with schemes,
their section rings, local rings and localization rings in the same mathematical size u.

Searches actually run using msearch.py (logged in the sandbox):

- LeanFinder: "For a quasi compact quasi separated morphism localization of global
  sections is base change, stalk of pushforward structure sheaf is localization, and
  the structure map is an isomorphism if and only if on stalks". Eight hits, including
  `StructureSheaf.isLocalizedModule_toPushforwardStalkAlgHom_aux` (affine-only) and
  morphism stalkwise-property lemmas. No complete match.
- Loogle: "AlgebraicGeometry.StructureSheaf.toPushforwardStalk, IsLocalization,
  Localization.lift". Zero hits; service reported unknown identifier `Localization.lift`.
  This query is inconclusive, not evidence of nonexistence.
- Mathlib grep: `isLocalization_basicOpen_of_qcqs|isIso_pushoutSection|` followed by
  `isLocalizedModule_toPushforwardStalk`, restricted to AlgebraicGeometry. Nineteen hits:
  principal-open qcqs localization, affine pushforward stalks, and flat base change.
  They supply components, not the whole normalized comparison and sheaf criterion.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for local-comparison,
  pushforward-stalk and qcqs-functions terms; rg for this exact node id upstream;
  and `dag/lean_names_upstream.json` for related localization/stalk names. Read
  `WeilConjectures.AlgebraicGeometry.AffinePushforwardStalkLocalization` in full: its
  `IsAffineHom f` premise excludes the nonaffine qcqs case here. No duplicate found.
  Also read the current `RegularPointBlowupFunctions` consumer: its localization and
  stalk uses require the maps normalized here; it introduces no replacement notion.

Source checked: `literature/stacks-project/coherent.tex`, the full statement of
`lemma-flat-base-change-cohomology` (Tag 02KH), part (2), degree zero. No source
hypothesis beyond qcqs f and the automatic flatness of localization was dropped.

Validation: scompile.py compiled the initial final statement cleanly (sandbox and
library module, about two seconds each). The first iteration exposed two elaborator
carrier-matching failures; using the actual pushforward germ in the denominator and
an explicit `@id` carrier conversion fixed them without changing the mathematics.
The expanded explicit dependency imports and final delivery passed the required dry run:
`OK (dry run): commit 7401671342d passes the preflight and compiles; nothing pushed`.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by NK

This is a clause-by-clause self-audit of the node and final module. The dispatch brief
requires this worker to deliver itself and prohibits starting another agent; the
maintainer's independent reading remains the delivery review. No independent reader
is claimed in this section.

Rechecked the exact hypotheses, the two section identifications, the orientation of both
pullback projections, and the order of the stalk isomorphisms. Checked that the coefficient
map is B → Γ(base change), that e.symm gives the requested germ-to-fraction direction,
and that the coefficient equation uses the stalk map of `f.c`, not f's map at a point
of Y. Checked that the criterion quantifies over all affine neighborhoods of every point,
and that σ covers arbitrary opens and has both inverse laws and restriction naturality.
Checked that normalized q and l in the further-localization square are unique by the
existing universal properties, and that arbitrary localization presentations include
both the ordinary fraction ring and the actual local ring. No mathematical mismatch
required a statement correction. No extra premise on denominators or prime fibres was
introduced. Every helper belongs to this one node and has constructed data.
