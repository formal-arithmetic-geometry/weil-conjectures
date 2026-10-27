## Worker report

The module `Sheaf.Topology.InjectiveSheafCotangentRoof` states the complete
injective ring-sheaf differential sequence, polynomial quotient resolutions,
canonical roof, derived arrow identification, and compatibility with open-subspace
restriction. Its only postponed proof is
`TopCat.SheafCotangent.exists_injectiveCotangentRoof`. All definitions have real
construction data. The auxiliary structures present the canonical objects by
normalized universal maps and generators; no object is selected from an unnormalized
existence theorem. The node's mathematical statement and dependency lists are unchanged.

Hypotheses and clauses, in statement order:

| Node text | Lean rendering |
| --- | --- |
| Topological space T | `{T : TopCat.{u}}`, with arbitrary universe `u` |
| Commutative ring sheaves A, B, C | `{A B E : T.Sheaf CommRingCat.{u}}`; `E` denotes the node's C |
| Maps A → B → C | `(f : A ⟶ B) (j : B ⟶ E)` |
| j injective | `hj : ∀ V : (Opens T)ᵒᵖ, Function.Injective (j.hom.app V)`; injectivity of a sheaf map means sectionwise injectivity |
| Use the standard resolutions and K | `C : Algebra.CotangentResolution.Coherence`, `S : Comparison C`, `F : FlatFunctorialModel C S`; `standardSheafComplex C S` is the dependency's actual normalized K |
| P, Q, S, R | `(S.sheaves T (Arrow.mk f)).standard`, the same expression for `f ≫ j`, `𝟙 B`, and `j` |
| Qbar and Rbar are degreewise tensor quotients | `injectiveQuotient C S F f j` and `injectiveQuotient C S F (𝟙 B) j` are pushouts of simplicial ring sheaves along the actual standard map and augmentation; functor-category pushouts are degreewise, and ring pushouts are algebra tensors |
| Agree with sheafification of sectionwise tensors | `InjectiveQuotientModel.presheaf`, `coordinate`, `restriction`, `sheafification`, `tensor_formula`; the last formula fixes the sheafification unit on every pure tensor |
| Sectionwise polynomial resolutions before sheafification | `InjectiveQuotientModel.polynomial_resolution`, using the dependency's exact `IsPolynomialResolution` on `injectiveSectionQuotient`; both Q and R instances occur in `InjectiveCotangentRoof` |
| Augmentation quasi-isomorphisms after sheafification | `augmentationQ_quasiIso`, `augmentationR_quasiIso`, on the actual alternating additive augmentations `injectiveQuotientAugmentation` |
| T_Q and T_R | `QuotientDifferentials` uses `differentialSheaf` (the existing relative sheaf differential tensor); `termIso` identifies every term and `operator` fixes all simplicial maps on universal differentials. `quotientDifferentialComplex` is the existing `negativeComplex`, hence alternating faces, degree -n and zero positive degrees |
| First term K[B/A] tensor_B C | `(D.E.mapHomologicalComplex (.up ℤ)).obj (standardSheafComplex C S (Arrow.mk f))`, with the recorded `DerivedChangeOfRingsCochainModel`'s actual ordinary extension functor and its prescribed object function `D.obj_eq` |
| i is the standard functoriality map | `first : StandardLinearization C S (injectiveTargetSquare f j) D`; the dependency fixes its pure tensor formula and standard derived interpretation |
| q induced by Q → Qbar and universal differentials | `quotientArrow`, `quotientArrow_formula` on every local polynomial differential |
| Degreewise short exact sequence | `zero` and `shortExact : ∀ i : ℤ, (ShortComplex.mk ...).ShortExact`; this retains mono, exactness, and epi in every degree of sheaf modules |
| Canonical Qbar → Rbar | `quotientMap_left`, `quotientMap_right`, `quotientMap_augmentation`; the two universal-leg equations uniquely fix the pushout map |
| Canonical alpha and beta | `alpha_formula`, `beta_formula` specify their action on every local differential generator, using the universal quotient arrow and the fixed `quotientMap` |
| Both roof maps quasi-isomorphisms | `alpha_quasiIso`, `beta_quasiIso` |
| Derived alpha-inverse beta is an isomorphism | `derivedIso`, with `derivedIso_roof : derivedIso.hom ≫ Q.map alpha = Q.map beta`; because alpha is a quasi-isomorphism, this is exactly the indicated inverse roof |
| Roof carries q to canonical base-ring arrow | `baseArrow_formula` identifies the standard base-ring functoriality map; `arrow_square` is the equality already on chain maps; `derivedIso_arrow` is the requested equality after localization |
| Sequence, roof and equality commute with open restrictions | The theorem quantifies over every `U : Opens T` and every presentation `D'` of scalar extension on U, and produces the restricted roof and `InjectiveRoofOpenRestriction`. `roofOpenRings` and `roofOpenComplex` are literal restriction to the open subspace, using Mathlib's `IsOpenEmbedding.sheafPullback`. The comparison isomorphisms are normalized on quotient tensors and differential generators. `first_square`, `quotient_square`, `alpha_square`, `beta_square`, `base_square` identify the entire sequence and roof. The chain and derived equalities therefore restrict: localization of commuting squares preserves composition, and inverses of commuting isomorphisms commute |
| No flatness of C/B | There is no flatness hypothesis on `j`, no flatness field for `E/B`, and no flat base change is used to define the sequence |

The parameters C, S, F, D and D' are presentations of the recorded standard and
ordinary tensor constructions. They impose no extra ring-map property. The
coefficient derived-category universe is `u + 1`; all variables and universes
are explicitly bound (`set_option autoImplicit false`). The module supplies
canonical ring sheafification and the site-presentation colimit instance, using
existing Mathlib constructions, rather than assuming pushouts as an extra hypothesis.

Dependency declarations used:

- `Sheaf.Topology.StandardSheafCotangentFlatModel`:
  `standardSheafComplex`, `StandardPolynomialMap`, `StandardLinearization`,
  `FlatFunctorialModel`, `scalarExtensionSection`, and their normalized fields.
- `Sheaf.Topology.SheafCotangentComparison` (publicly imported by the preceding
  module): `Comparison`, `sectionArrow`, `restrictionSquare`, `polynomialSection`,
  `differentialSheaf`, `differentialSection`, `sectionElement`, `SheafModel`,
  `StandardSheafModel`, `MapModel`.
- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Coherence`, `standardTerm`, `standardSquareMap`, `Augmentation`,
  `IsPolynomialResolution`, `negativeComplex`, `complexGenerator`.
- `Sheaf.RingTheory.InjectiveStandardResolutionQuotients`:
  `quotientAugmentation`; proof input
  `isPolynomialResolution_quotient_of_injective`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, its universal
  derivation and linear-map/derivation equivalence, through the dependency's
  existing differential tensor constructions; no second Kahler notion.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `QuasiIso` and localization of quasi-isomorphisms.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, `E`, `obj_eq`.
- All already-stated proof dependencies are imported, directly or through the
  public standard-model imports. The specific tensor, differential-cokernel and
  open-restriction proof modules are imported non-publicly:
  `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`,
  `Sheaf.CategoryTheory.Sites.SheafifiedDifferentialsCokernel`,
  `Sheaf.CategoryTheory.SiteModuleSliceSheafification`. Mathlib's polynomial
  differential basis, underlying-set sheafification comparison, and exact
  module sheafification modules are also imported for the proof plan.

Edge cases checked mathematically before finalizing the statement:

- Empty topological space and empty opens: ring sheaf sections are zero rings;
  no nonemptiness assumption occurs, and restriction to the empty open is covered.
- B = C with j the identity: the quotient standard simplicial algebra is constant
  B, so its relative differential complex is zero. The short exact sequence has
  the expected identity first arrow, up to its prescribed presentations.
- A = B: the two independent quotient constructions and their canonical roof
  remain present, without deleting the identity-base case.
- A → B need not be injective; only j is required injective.
- Nonflat injective map Z → Z × F₂ (diagonal): admitted. The differential sequence
  is checked by polynomial coordinates, so it does not assume this map flat.
- Zero coefficient ring: admitted; an injective B → 0 forces B = 0 and all
  differential module statements specialize appropriately.
- Infinite variable sets and all negative degrees: no finiteness or lower-bound
  hypothesis occurs. Positive terms are the zero extension in `negativeComplex`.
- Restriction to the whole open and to nested opens uses the same normalized
  tensor and differential formulas, including the identity restriction case.

Searches (all before choosing this construction):

- `msearch.py ... leanfinder`: "Injective ring sheaf standard cotangent
  differential short exact sequence quotient resolution roof". Eight hits about
  naive cotangent modules of presentations and smoothness, none about this roof.
- `msearch.py ... loogle`: "KaehlerDifferential, ShortComplex.ShortExact".
  No match; the latter short name was not recognized by the service.
- `msearch.py ... grep`: "cotangent.*(roof|injective)|quotientAugmentation" in
  `RingTheory`. Twenty-five hits about ring-presentation cotangent modules,
  none stating the sheaf sequence or roof.
- `msearch.py ... leansearch`: "cotangent complexes sheaves rings transitivity
  injective short exact quotient resolution". Eight hits about injective
  resolutions and naive cotangent modules, none equivalent to the item.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for injective cotangent/roof
  and `quotientAugmentation`: found the recorded sectionwise
  `InjectiveStandardResolutionQuotients` dependency and unrelated uses of the
  phrase, no duplicate sheaf-roof statement. Search for the exact blueprint id
  in `lean/WeilConjectures` found no declaration.
- Read the live server versions of the standard-model and comparison modules
  via `scompile.py --source` to confirm the dependency interfaces.

No statement fault or STATEMENT-DISPUTED issue was found. No new DAG nodes or
dependency-record repairs are needed: the helpers belong to the canonical
sequence-and-roof construction of the item itself.

## Second reading by Q13

A separate clause-by-clause reading of the node, Stacks 08SD/08SE/08SZ and the
finished module checked all fields listed above. No other agent was started,
as required by the dispatcher's explicit instruction; the maintainer supplies
the independent review of this delivery.

The reading caught the need to normalize the open restriction isomorphisms,
rather than merely assert unrelated isomorphisms of additive complexes. Added
`first_generator`, `middle_generator`, `last_generator`, both quotient generator
fields, both algebra tensor fields, and the augmentation/quotient-map squares.
Consequently all comparison maps are the canonical restriction maps, and their
values on c tensor dz also determine their coefficient linearity. The first
map is the dependency's `StandardLinearization`; the quotient arrow and both
roof maps have explicit differential formulas. The derived roof equation is
in D(E), not D(B), and the claimed derived isomorphism is explicitly supplied,
not replaced with only cohomology isomorphisms. No node statement changes were
made. All helper data are actual constructions or normalized presentations;
the only `sorry` is the final theorem's whole proof.
