## Worker report

Item: `lem-sfb-dvr-unit-root-normalized-lift`, group Q140, stage 2.

The module `Sheaf.RingTheory.DvrUnitRootNormalizedLift` states
`RingTheory.exists_dvr_unit_root_normalized_lift`. Its only proof is `by sorry`.
There are no definitions, new nodes, dependency repairs, or statement changes.
The node copy changes only `lean`. The complete seven-step node proof is in the
theorem docstring, with the proof dependencies named. Statement dependencies are
public imports; the stated proof dependencies are plain imports.

I read the node, all five statement-dependency nodes and their recorded declarations,
the proof-dependency records, and Stacks `more-algebra.tex`, `lemma-abhyankar`
(Tag 0BRM), especially its first claim. That claim explicitly adjoins a root of a
unit, chooses compatible normalization branches, and asserts ramification index one
and finite separable residue extensions. The node correctly extracts this construction
without imposing the later Abhyankar hypotheses on the original residue extension.
No statement fault or dispute was found.

The following table accounts for every hypothesis and conclusion.

| Node clause | Lean rendering |
| --- | --- |
| S and T are discrete valuation domains | `S : Type u`, `T : Type v`, each with `CommRing`, `IsDomain`, `IsDiscreteValuationRing`. The last class means a local principal ideal domain with nonzero maximal ideal. |
| Injective local S -> T | `[Algebra S T]`, `hinj : Function.Injective (algebraMap S T)`, `[IsLocalHom (algebraMap S T)]`. For local rings `IsLocalHom` is equivalent to contraction of the target maximal ideal being the source maximal ideal. |
| Compatible fraction fields N contained in F | Fields `N : Type w`, `F : Type z`, `[Algebra S N] [IsFractionRing S N]`, `[Algebra T F] [IsFractionRing T F]`, `[Algebra N F]`; `[Algebra S F]` and the two towers `S,T,F` and `S,N,F` encode the commuting square. Field ring homomorphisms are injective. |
| h >= 1, h invertible in S, u a unit of S | `(h : ℕ) (hh : 1 ≤ h) (hunit : IsUnit (h : S)) (u : Sˣ)`. |
| Finite separable algebraic N'/N and F'/F | Existential `N' : Type w`, `F' : Type z`, `Field` and base `Algebra` structures, with `FiniteDimensional N N'`, `FiniteDimensional F F'`, and the two `Algebra.IsSeparable` clauses. Separable here already implies algebraic; finite means finite dimensional, not finite cardinality. |
| Compatible N' -> F' extending N -> F | `(i : N' →+* F')` and `i.comp (algebraMap N N') = (algebraMap F F').comp (algebraMap N F)`. Since N' and F' are fields, i is injective. The additional S- and T-algebras on N', F' are pinned to the respective fraction-field maps by `IsScalarTower`. |
| r in N' with r^h = u | `(r : N')` and `r ^ h = algebraMap S N' (u : S)`. |
| Generated subfields N(r) = N', F(i(r)) = F' | `IntermediateField.adjoin N ({r} : Set N') = ⊤` and `IntermediateField.adjoin F ({i r} : Set F') = ⊤`. These are generated fields, not merely subalgebras or unspecified simple extensions. |
| D and E the integral closures | Existential `D : Subalgebra S N'`, `E : Subalgebra T F'` with equations `D = integralClosure S N'`, `E = integralClosure T F'`. These equalities name the actual Mathlib constructions, with no private replacement. |
| Canonical D -> E induced by i | `d : D →+* E` with `∀ x : D, (d x : F') = i (x : N')`. Inclusion E -> F' is injective, so this equation determines d uniquely. It is not an arbitrary normalization map. |
| Maximal ideals a,b, b intersect D = a | `a : Ideal D`, `b : Ideal E`, class witnesses `a.IsMaximal`, `b.IsMaximal`, and `hab : a = b.comap d`. |
| a intersect S = m_S, b intersect T = m_T | `a.comap (algebraMap S D) = IsLocalRing.maximalIdeal S`, and the corresponding equality over T and E. |
| S1 = D_a, T1 = E_b are DVRs | The types are literally `Localization.AtPrime a` and `Localization.AtPrime b`, with existential `IsDiscreteValuationRing` witnesses. Domain and local-ring structures are Mathlib's existing instances for prime localizations of subalgebras of fields. |
| Canonical S -> S1 and T -> T1 | Algebra structures on the two actual localizations, with their `algebraMap`s equal to the composite of the integral-closure structure map and the localization map. Thus the existential algebra structures cannot change these arrows. |
| Canonical local S1 -> T1 | The existing `Localization.localRingHom a b d hab`; no new localization-map construction. Its `IsLocalHom` clause renders locality explicitly. |
| All four maps injective and local | Original map: the hypotheses. Horizontal maps: explicit `Function.Injective` conclusions and existential `IsLocalHom` witnesses. Localized vertical map: explicit `Function.Injective` and `IsLocalHom` clauses. |
| The square commutes | `(Localization.localRingHom a b d hab).comp (algebraMap S (Localization.AtPrime a)) = (algebraMap T (Localization.AtPrime b)).comp (algebraMap S T)`. |
| r belongs to S1 inside N' | `j : Localization.AtPrime a →+* N'`, specified by `∀ x : D, j (algebraMap D (Localization.AtPrime a) x) = (x : N')`, and `∃ r₁ : Localization.AtPrime a, j r₁ = r`. The restriction uniquely determines the canonical fraction embedding; its injectivity follows from its restriction to D and the fraction description of the localization. Thus this is actual membership in D_a, not an unrelated root in another ring. |
| m_S S1 = m_S1 | `(IsLocalRing.maximalIdeal S).map (algebraMap S (Localization.AtPrime a)) = IsLocalRing.maximalIdeal (Localization.AtPrime a)`. |
| m_T T1 = m_T1 | The identical ideal-map equality over T and b. |
| S1 residue field finite separable over S residue field | `FiniteDimensional (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField (Localization.AtPrime a))` and the corresponding `Algebra.IsSeparable`. The canonical residue algebra is Mathlib's instance induced by the pinned horizontal algebra map and its `IsLocalHom` witness. |
| T1 residue field finite separable over T residue field | The two corresponding clauses over T and b. |
| No finiteness or residue separability of F/N | There is no such hypothesis. Only its field-algebra structure and compatibility with the original DVR maps are assumed. |

Existentially naming D,E, the horizontal algebra structures, d, and j does not add
assumptions or strengthen the mathematical assertion: their displayed equations
uniquely specify the usual integral closures and canonical maps. In particular,
none is a free map used to replace a canonical construction. No `let`, hidden
`show ... from`, file-local notation, private definition, or local instance occurs.
All four universes and every variable are explicitly bound; `autoImplicit` is false.

Dependency declarations used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`, the
  exact `mathlib_match` of `def-sc-discrete-valuation-ring`; its domain hypothesis
  is separately bound, as required by the class signature.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`, the recorded field-extension
  definition `def-pc-field-extension`. `IsScalarTower` expresses compatibility.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`, the recorded declaration
  of `def-weil-pbc-separable-algebraic-extension`; its docstring and
  `Algebra.IsSeparable.isAlgebraic` show algebraicity is included.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, the recorded
  declaration of `def-weil-pbc-integral-closure`, with carrier `{x | IsIntegral S x}`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, the
  recorded localization of `def-weil-pbc-localization-at-prime`, and its existing
  canonical `Localization.localRingHom` with contraction equality argument.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: `IsLocalRing.ResidueField`,
  literally quotient by the maximal ideal, and the canonical residue-field
  `Algebra` instance for a local algebra map. This is the residue notion cited
  in the localization node, with no alternate residue field construction.
- `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`: `IntermediateField.adjoin`,
  the standard generated subfield, used for the two explicit generated-field clauses.
- `Mathlib.RingTheory.Localization.FractionRing`: `IsFractionRing` for the given
  compatible fraction fields.

The proof imports include the recorded
`AlgebraicGeometry.exists_finite_etale_normal_generic_components` from
`Sheaf.AlgebraicGeometry.FiniteEtaleNormalGenericComponents` and
`AlgebraicGeometry.Scheme.etale_trait_stalk` from
`WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTraitStalk`. I read their full
signatures and proof docstrings. Remaining Mathlib proof-dependency matches are
imported from their recorded files (PID, rational-root normality, affine stalks,
function fields, normal localizations, standard étale algebras, finite integral
generators, maximality over maximal ideals, and separable étale residue fields).
No additional statement interface is needed.

Edge cases checked mathematically before writing:

- h=1 is allowed. Take N'=N and F'=F with r=u. A DVR is integrally closed,
  so the integral closures identify with S,T and the chosen localizations give
  the original local square. Both residue extensions are identities.
- If u already has an h-th root in N, the degree-one extension is allowed;
  neither extension is required to have degree h or to be nontrivial.
- The zero ring and fields as DVRs are excluded exactly by the DVR definition;
  there is no extra nontriviality or residue-characteristic condition.
- Positive residue characteristic dividing h is excluded by `hunit`, exactly as
  intended. Characteristic zero and positive characteristic prime to h are covered.
- S=T with the identity map is allowed. The same compatible branches can be used.
- F/N can be transcendental, infinite, or have inseparable residue extension.
  The argument selects the upper unit-root field first and its lower generated
  subfield; it does not require linear disjointness or separability of F/N.
- Multiple normalization branches are allowed: a,b are existential and constrained
  by contraction, not prespecified or assumed unique.
- Independent input universes u,v,w,z are retained. Finite algebraic extensions
  N',F' can be represented in the universes of their base fields, respectively;
  no equality of the four input universes is imposed.

Searches for an existing exact statement:

1. `msearch.py ... leanfinder "Compatible normalized integral closure DVR extensions obtained by adjoining an invertible degree root of a unit"`: 8 hits, including `ValuationSubring.algebra`, `galLift`, `IsDedekindDomainDvr.isIntegrallyClosed`, normal-closure instances, and `IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow`. None constructs both selected normalized DVR branches and both residue extensions.
2. `msearch.py ... loogle "IsDiscreteValuationRing, integralClosure"`: 0 hits.
3. `msearch.py ... grep "unit.*root|root.*unit|integralClosure.map" RingTheory`: 25 hits, including general integral-closure transport, Hensel roots, and roots of unity; none is the diagram statement.
4. `msearch.py ... leansearch "Adjoining a root of a unit to a local inclusion of discrete valuation rings produces compatible localized integral closures with finite separable residue extensions"`: 8 hits, including `IsLocalization.Away.integralClosure`, `adjoin_le_integralClosure`, `IsAdjoinRoot.mkOfAdjoinEqTop`, and `IsDedekindDomainDvr.isIntegrallyClosed`. These concern individual constructions, not the compatible normalized diagram.
5. `rg -n 'unit.root|unitRoot|normalized.lift|normalizedLift|lem-sfb-dvr-unit-root-normalized-lift' lean/WeilConjectures lean/Sheaf dag/lean_names_upstream.json`, followed by targeted `rg -n 'dvr.*unit.*root|DvrUnitRoot|unit_root_.*diagram|NormalizedLift'` in the RingTheory directories: found upstream local root-square and weakly unramified diagram results, whose full signatures were inspected.
6. In particular `RingTheory.dvr_etale_unit_root_diagram` supplies an arbitrary local DVR square and a generated algebra presentation, and `RingTheory.dvr_unit_root_weakly_unramified_diagram` adds one maximal-ideal extension equality. Neither states both normalized integral closures with selected primes, the two generated field equalities, and both finite separable residue extensions. They are not exact existing matches.
7. Exact identifier searches for `exists_dvr_unit_root_normalized_lift` and the item id in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declaration.

Validation: `scompile.py Q140 lem-sfb-dvr-unit-root-normalized-lift` compiled the
module in both sandbox and library module modes against the published server
build. Both passed, with no errors or warnings (17.7s and 3.8s).

## Second reading by Q140

This is a second self-reading of the node and complete Lean signature, not a claim
of an independent agent review: the dispatcher's brief forbids starting other
agents, and assigns the independent review to the maintainer after delivery.

I checked the lower and upper generated-field equalities separately, the direction
of the contraction `a = b.comap d`, the separate contractions to the two original
maximal ideals, and all four injective/local arrows. I also traced each canonical
map: d is fixed inside F', the two horizontal algebra maps are fixed by localization,
and the vertical localization map uses exactly Mathlib's `localRingHom` and hab.
The membership witness uses the embedding of the actual D_a in N' fixed on D.
The residue instances use the same horizontal maps, so their finiteness and
separability concern the stated quotients with their canonical extensions.

The two DVR witnesses carry no extra assumptions on the original diagram. The
four universes remain independent. All seven natural-language proof steps and
all stated proof-dependency imports are present. No mismatch or correction was
found on this rereading; the first written signature compiled without repairs.
