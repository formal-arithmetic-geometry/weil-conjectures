## Worker report

The delivery states `AlgebraicGeometry.ProEtale.pullback_constantModelConstructible` in
`Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible`. Its only theorem proof is
`sorry`. Two real auxiliary definitions package exactly this node's construction and
assertion; they introduce no replacement module, scalar-ring, or constructibility notion.
No natural-language statement correction or dependency repair is made.

Clause-by-clause reading:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The chosen algebraic closure is the upstream
  `PadicAlgCl ℓ`, used by the existing coefficient declarations. This is the existing
  encoding of the fixed algebraic closure, rather than an additional hypothesis on it.
- The condensed coefficient ring is `L : Sheaf (coherentTopology Profinite) RingCat`;
  its underlying abelian sheaf and canonical internal multiplication are supplied by
  `sheafCompose ... (forget₂ RingCat Ab)`. The displayed `IsCommMonObj` instance states
  commutativity, which every admissible case has.
- `hL` lists precisely the allowed rings. Its first alternative is a finite commutative
  ring `A`, with `∃ n, ∀ a, (ℓ ^ n) • a = 0`, and the constant ring sheaf with value A.
  A finite discrete ring has continuous sections exactly locally constant A-valued
  functions, so its continuous condensed ring is this constant sheaf. The isomorphism
  permits the chosen presentation of that same condensed ring. No nontriviality is
  imposed; exponent zero includes the zero ring.
- The next alternatives are `padicIntCondensedRing`, `padicCondensedRing`, a finite
  intermediate field E in `PadicAlgCl ℓ` with `FiniteDimensional ℚ_[ℓ] E` and either
  `padicIntegersCondensedRing ℓ E` or `padicSubfieldCondensedRing ℓ E`, and finally
  `padicAlgClCondensedRing ℓ`. The last declaration uses only continuous functions
  whose images lie in a finite subextension. It is not the full continuous-function
  condensed ring of the algebraic closure. The finite extension has the topology
  induced by its embedding in that fixed algebraic closure; its integers are the
  upstream norm-at-most-one subring.
- `ConstantModelPullbackStatement` unfolds the scheme/module quantifiers. Both
  Y and Y' have `[CompactSpace] [QuasiSeparatedSpace]`, with no condition on the
  morphism g beyond `g : Y' ⟶ Y`. These are the recorded qcqs predicates.
- The coefficient module categories are literally
  `Mod (Sheaf (Scheme.ProEt.topology Y) Ab) (condensedRingObj Λ Y)` and its analogue
  on Y'. `condensedRingObj` is the recorded point-pulled coefficient ring.
  `CondensedRing.upperStar Λ g` is the recorded underived ringed-topos module inverse
  image, including extension of scalars along the canonical coefficient comparison.
- `IsConstantModelConstructible Λ Y M` is the precise recorded hypothesis. The
  first conjunct is `IsConstantModelConstructible Λ Y' ((upperStar Λ g).obj M)`.
- The more-precise clause quantifies over any given finite locally closed scheme
  stratification `S : Y.FiniteLocallyClosedStratification`, and separately assumes
  `hS : ∀ a, Topology.IsConstructible (S.stratum a)`. Thus the weaker bare
  stratification interface is used exactly as recorded, with the required
  constructibility hypothesis explicitly present.
- `constantModelPullbackStratification S hS g` combines those given fields into the
  existing `Scheme.Stratification` and applies `Scheme.Stratification.pullback`.
  Its number of strata is definitionally S.n, its subsets are inverse images, its
  schemes are `pullback (S.immersion a) g`, and its immersions are `pullback.snd`.
  Its structure fields supply local closedness, constructibility, pairwise
  disjointness, and covering of Y'. No abstract alternative stratification is chosen.
  The factors in this fibre product are ordered Y_a then Y'; this is the same
  base-changed subscheme Y' ×_Y Y_a via the canonical symmetry.
- `U : ∀ a, Scheme.Cover Scheme.proetalePrecoverage (S.domain a)` is the whole
  given pro-etale cover on every stratum. The output uses exactly
  `(U a).pullback₂ (pullback.fst (S.immersion a) g)`. This is a cover as a typed
  object, with exactly the same index type and with members
  `U_{a,i} ×_{Y_a} (Y_a ×_Y Y')`. The covering map is the second projection.
- `P a i : Mod Ab (scalarRingObj Λ)` is the ordinary scalar module in the
  existing internal-module encoding of modules over the scalar ring Λ(*).
  `Mod.IsFinitelyPresented (scalarRingObj Λ) (P a i)` is assumed for every member.
  There is no uniform rank bound, choice of a new module, or freeness hypothesis.
- The given local-model isomorphisms use `finiteConstantScalarExtension Λ (U.X i)`
  on `P a i`. That existing functor is exactly Λ_U ⊗_{Λ(*)_U} P_U, rather than an
  arbitrary locally finitely presented coefficient module. The conclusion uses the
  very same expression on the base-changed cover member and the *same* `P a i`.
  Its left-hand side is restriction of g* M first to the canonical pulled-back
  stratum, then to that member of the base-changed cover. `Nonempty ( ... ≅ ... )`
  expresses existence of each required module isomorphism.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` and its public import
  `ContinuousCoefficientUniverse`: the universe-general continuous condensed-ring
  construction for `sk-def-sfb-condensed-ring`; imported through FiniteConstantLocalModel.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicIntCondensedRing`, `padicCondensedRing`,
  `padicSubfieldCondensedRing`, `padicIntegersCondensedRing`, and
  `padicAlgClCondensedRing` (the closed upstream binding of sk-def-sfb-qlbar-condensed).
- `Mathlib.Topology.Defs.Filter.CompactSpace` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated` and `QuasiSeparatedSpace`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, and the point-pullback comparison.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar` and the documented canonical composition/adjunction.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`,
  `IsConstantModelConstructible` (publicly imported by FiniteConstantLocalModel).
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification` and its field signatures.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`:
  `scalarRingObj`, `finiteConstantScalarExtension`,
  `HasFiniteConstantLocalModelOnCover`, and the recorded local-model equivalences.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`,
  `Scheme.ProEt.topology`, `Scheme.proetalePrecoverage`, and the inherited cover base change.
- The already-recorded `lemma-constructible-pullback-stratification` is added to
  stmt_deps because the real auxiliary definition uses its canonical
  `Scheme.Stratification.pullback` construction directly. It was already a proof
  dependency. Its module is `WeilConjectures.ConstructibleSheaf.Pullback`.
- Remaining stated proof dependencies are imported: the preimage theorem in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, and
  `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`.
  The coefficient-comparison dependencies are already in ModuleObject.Basic and Defs.

Source and edge checks: opened the current main-20261015 pullback proof paragraph
"Constructible complexes" and the complete source signatures/docstrings above. The
empty target and empty strata do not require a nonempty index, a positive number of
strata, or a positive rank. Empty covers of an empty stratum are permitted by the
cover type. P=0 and the zero coefficient ring are permitted. Identity g returns the
canonical identity base changes, without discarding the arbitrary chosen covers.
No smoothness, weak etaleness, finite type, or Noetherian assumption is imposed on g.
Finite extensions E=ℚ_ℓ and varying finite presentations across cover members are
included. The same universe u is used for schemes and covers, with Ab and ring
coefficients in u+1, following the published framework. No auto-bound variables.

Searches (2026-10-18):

- `msearch.py ... leanfinder "pullback preserves constructible modules with finite
  constant scalar models on strata"`: eight hits, including vector-bundle pullback,
  locally constant module functors, and ordinary sheaf/module pullback; no exact theorem.
- `msearch.py ... leansearch "pullback preserves constructible sheaves finite constant
  local models"`: eight sheaf-pullback/finite-limit hits; no exact theorem.
- `msearch.py ... loogle "SheafOfModules.pullback"`: twelve ordinary module-sheaf
  pullback and composition declarations; none is this condensed constructibility theorem.
- `msearch.py ... grep "IsConstructible|ConstantLocalModel" AlgebraicGeometry`:
  constructible images/preimages of subsets only, not this module-object statement.
- `rg` in upstream WeilConjectures and `lean/Sheaf` for the item id and for
  `finiteConstant.*[Pp]ullback|[Pp]ullback.*[Cc]onstantModel`: no exact existing theorem;
  the existing CondensedConstantConstructibility definitions are reused.
- `grep -rn` for the exact item id in upstream WeilConjectures: no hits.
- `rg` for all three new full-name suffixes in Mathlib, upstream WeilConjectures,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no name collisions.
- Related coefficient and stratification searches identified the already recorded
  interfaces; no new independent notion or new DAG node is needed.

## Second reading by Q29

This is the author's separate second reading; the maintainer supplies the independent
review under the dispatcher brief. Reopened the node and the complete written module.
The two substantive conclusions match: constructibility on the qcqs target, and models
for every given witnessing stratum/cover with each original P retained. Checked that
`pullback₂` projects to the new stratum, while `pullback.fst` maps the new stratum to
the old one; reversing those projections would type the wrong cover. The output
stratification constructor uses the given immersion's actual fibre product, so it does
not weaken the precise claim to existence of arbitrary strata. Checked all six
coefficient classes, the finite-extension condition, and the special finite-valued
algebraic closure. The finite constant-ring-sheaf representation is equivalent to the
finite discrete continuous condensed ring and preserves the scalar ring up to its
canonical isomorphism. No unrecorded source correction, extra mathematical assumption,
missing clause, or disputed statement was found. Compilation and preflight outcomes
are recorded below once complete.

## Validation

The prescribed scompile.py compiled both the sandbox check and the final module cleanly
(no compiler messages), in 7.3 s and 14.7 s respectively after slot acquisition.
The prescribed deliver2.py --no-push returned OK: preflight and per-file compilation
passed for dry-run commit f5829b1b47, with nothing pushed. No global build or direct
Git command was run, and no shared source was edited.
