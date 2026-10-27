## Worker report

The main module is `Sheaf.AlgebraicGeometry.SupportedFormalBlowupAlgebraization`,
with theorem `AlgebraicGeometry.AdicFormal.supportedFormalBlowupAlgebraization`.
Its only proof is `sorry`. The two definition modules contain actual diagrams,
ideal pullbacks, chart conditions and finite tower data; no construction uses sorry.
The original node statement is unchanged. Two missing definition nodes supply the
adic formal scheme and centered-tower interfaces under brief-stage2 §1(A).

Hypotheses and clauses, in order:

- A scheme X is the explicit `X : Scheme.{u}` binder, with all universes explicit
  and `autoImplicit false`. `AlgebraicGeometry.IsNoetherian X` is Mathlib's locally
  Noetherian plus compact condition, equivalent to the specified finite affine cover.
- Over Q is `toRat : X ⟶ Spec (.of (ULift.{u} ℚ))`. This includes any universe u.
  Quasi-excellence is `hQE : ∀ U : X.affineOpens, IsQuasiExcellent Γ(X,U.1)`.
- Z is the actual closed subscheme `I.subscheme`, with its ideal `I`; `hI` is the
  exact finite-type-with-finite-type-kernels `RingedSpace.IsCoherent` predicate.
- The completion is `AdicFormal.completion I`, the genuine diagram of closed
  schemes `V(I^(n+1))` with their canonical inclusions. Formal affines are compatible
  open charts `Spec(B/K^(n+1))` for Noetherian K-adically complete B; the affine
  chart squares are cartesian. A finite covering of every infinitesimal order is
  `AdicFormal.IsNoetherian`. This is the usual infinitesimal-system presentation
  of the ringed space whose structure sheaf is the inverse limit of these sheaves.
  Its affine rings are exactly the completed chart rings, not arbitrary parameters.
- Formal regularity is `AdicFormal.IsRegular`: every complete formal affine chart
  ring is an `IsRegularRing`. The ordinary notion is the dependency's exact
  `IsRegularScheme`. The singular locus used here is explicitly the set of points
  with nonregular local ring. For the quasi-excellent input it is the support of
  the reduced closed singular subscheme; the formal support is its inverse image
  on the canonical closed thickenings. No unrelated singular subscheme is chosen.
- Ordinary centers are `OrdinaryTower.center`, actual ideal-sheaf data, with
  `coherent` and `supported`: the extended I to a positive power is contained in
  the center ideal. The actual arrow is specified by `blowup` and `blowup_arrow`
  using the recorded ordinary blowup. Formal centers are compatible ideal-sheaf
  data `FormalTower.center`; `IsCoherentOpenIdeal` says the closed center factors
  through one finite order, precisely containment of a power of the definition
  ideal. `IsBlowup` uses blowup of Spec B followed by completion along extended K,
  compared over Spec B on every chart; it never blows up a finite quotient instead.
- The first two conjuncts give a completion partner for every ordinary and every
  formal tower, of the same arbitrary finite length r. `Completion.iso` identifies
  every level with its specified completion; `over`, `arrows` and `centers` state
  the structural-map and ideal equalities. No stage is contracted.
- The next two conjuncts give `Unique (OrdinaryIso T S)` and
  `Unique (FormalIso F G)` whenever two towers have the same completion partner.
  Each isomorphism preserves the base, all arrows and all ordered ideals. Thus
  these are a bijection of centered towers up to unique centered isomorphism,
  without making a noncanonical selection from existence.
- `c.CentersAgree` states for each i and every order N containing the whole open
  formal center that there is a unique center scheme isomorphism over T's level,
  and nonemptiness and `IsRegularScheme` are equivalent. This expresses the
  canonical identity of actual closed schemes, rather than equality of supports.
- The last implication uses the precise `X_sing ⊆ |Z|` stalkwise hypothesis;
  `IsRegular (F.level (Fin.last r))` and `F.HasSingularCenters` imply terminal
  ordinary regularity and `T.HasSingularCenters`. The final reduced implication
  gives `T.HasNowhereDenseCenters` in each ordinary level separately.

Dependencies read and used:
`Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`;
`Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`;
`Sheaf.AlgebraicGeometry.CoherentFiniteType` and its public upstream coherence
import: `RingedSpace.IsCoherent` (not just quasi-coherent finite type);
`Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, `IsAdicComplete`;
`Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`;
`WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`;
`Mathlib.AlgebraicGeometry.Properties`: `IsReduced`.
The construction also uses Mathlib's `IdealSheafData.subschemeFunctor`, powers,
comap and subscheme inclusions, and the upstream ideal-to-module construction.
Every proof dependency that has a recorded module (including closed-audit modules)
is imported non-publicly in the theorem module. The remaining unstated proof
prerequisites require no declaration to type this statement and are not duplicated.

Edge cases checked: r=0 has Fin 1 levels and Fin 0 centers; X empty has an empty
formal affine covering; I=unit has empty thickenings and only unit supported
ordinary centers; I=zero gives the constant infinitesimal system; nilpotent I
stabilizes. A unit center remains a stage and its blowup is identity; a supported
zero center has empty blowup, and subsequent empty levels remain indexed. The
ideals (t) and (t²), even when their blowups are isomorphic, remain distinct
center fields. No point, nonzero ring, nonempty center or reduced input is assumed.

Searches actually run (complete wire results in searches.jsonl):
LeanFinder, “Completion gives a bijection between supported blowup towers of a
Noetherian scheme and formal blowup towers of its adic completion, preserving
center ideals”: 8 completion-ring lemmas, no formal scheme/tower declaration.
Loogle, `FormalScheme, Spf, AdicCompletion, blowup`: unknown FormalScheme, 0 hits.
LeanSearch, “Noetherian adic formal scheme as a compatible system of infinitesimal
thickenings, supported coherent open ideals and formal blowup”: 8 hits, namely
Noetherian-scheme recursors, adic topology, formally unramified and completion;
none supplies the formal scheme, formal blowup or centered tower notion.
Mathlib grep `FormalScheme|Spf|formalBlowup|formalCompletion` initially gave 25
unrelated modular-form matches; refined word-boundary grep in AlgebraicGeometry
returned 0. LeanFinder for finite ordinary/formal towers retaining ordered ideals
returned prime-chain and adic ring results, no tower declaration. Source rg over
WeilConjectures and Sheaf found module completion systems but no formal scheme or
formal blowup. DAG grep identified formal-geometry theorem nodes but no definition
node for these interfaces; normalized and logarithmic towers are different notions.
`tools/blueprint_refs.py search 'formal scheme'` returned zero matching units;
ancestor is `lem-per-artin-gabber-affine-curve`. No existing declaration states the
assigned theorem. The current Temkin PDF was opened online, specifically §§2.4.1--
2.4.11 and Lemma 2.4.3(i)--(ii), including its finite-induction proof, on 2026-10-24.

## New nodes

`def-per-noetherian-adic-formal-system` owns
`Sheaf.AlgebraicGeometry.NoetherianAdicFormalSystem`. It defines the canonical
infinitesimal completion diagram, formal affine charts with cartesian transition
squares, finite covers, coherent open ideal systems, their center orders, formal
regularity, reducedness, quasi-excellence, completed ideals and formal blowups on completed ordinary charts.
Source: Temkin §§2.4.1--2.4.9. The recorded LeanSearch/Loogle/LeanFinder/grep searches
found only underlying completion-ring and scheme primitives. No existing node
provides this formal geometry interface.

`def-per-supported-centered-blowup-towers` owns
`Sheaf.AlgebraicGeometry.SupportedCenteredBlowupTowers`. It defines finite ordinary
and formal towers with their centers, their base- and ideal-preserving isomorphisms,
completion comparisons, canonical center-agreement condition, singular support,
and nowhere density. Source: Temkin §§2.2.1--2.2.2, 2.4.7--2.4.11 and Lemma 2.4.3.
The same actual search logs plus the dedicated centered-tower LeanFinder search
find no declaration of this centered ordinary/formal correspondence. The existing
normalized towers include normalization and different center restrictions, so
cannot serve as an ordinary blowup tower without changing this node's statement.

## Second reading by Q51

This is a worker rereading; the maintainer supplies the independent delivery review.
The base/noetherian/Q/quasi-excellent/coherent-ideal assumptions and every conclusion
were matched to the theorem above. Rereading found the formal chart definition
needed cartesian transition squares, which were added, so an unrelated open chart
at each quotient order cannot be mistaken for one formal open. It also found the
point-map application in singular support needed one more parenthesis; that was
corrected before compilation. Completion compares actual schemes and ordered
ideals, not just arrows up to isomorphism. The two existence clauses and two unique
isomorphism clauses cover both directions, while the terminal conditional has
exactly the singular-support and reducedness hypotheses of the original node.
No original DAG statement was corrected, no dependency interface was replaced,
and there is no STATEMENT-DISPUTED finding.
