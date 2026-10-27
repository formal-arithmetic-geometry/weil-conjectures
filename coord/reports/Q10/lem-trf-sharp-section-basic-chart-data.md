## Worker report

The module `Sheaf.AlgebraicGeometry.SharpSectionBasicChartData` states
`AlgebraicGeometry.FineFan.sharp_section_basic_chart_data`, with its entire proof
postponed by `sorry`. It introduces no definitions. The node's statement, dependencies,
and proof are unchanged; only its `lean` record is added.

Read source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.1--3.1.4 and
Lemma 3.1.8(i)--(ii), printed pp.98--99 (PDF pages 104--105), including the proof.
The source constructs the prime as the complement of the inverse image of units;
sharp stalks turn “unit” into “identity”. It extends the germ maps by localization
and factors through the quotient by units. The node expands the sectionwise
construction and compatibility implicit in that argument.

Notation follows the recorded dependencies: monoids are multiplicative, additive
zero is `1`, additive `p-na` is `of p * (of a ^ n)⁻¹`, and sharpening is
`Associates`. This is a change of notation only.

Hypotheses, individually:

| Node | Lean |
| --- | --- |
| A topological space T with a sheaf A of commutative monoids | `T : SheafedSpace CommMonCat.{u}` bundles exactly these data, without any locality or affine assumption. |
| Sharp stalks | `hT : ∀ x : T, IsSharp (stalk T.presheaf x)` |
| Fine monoid P | `P : Type u`, `[CommMonoid P]`, `hP : IsFine P` |
| P is sharp | `sP : IsSharp P` |
| Homomorphism to global sections | `φ : P →* T.presheaf.obj (op ⊤)` |

Conclusions, individually and in their order in the theorem:

| Node | Lean |
| --- | --- |
| All open-section monoids are sharp | First conjunct `∀ U : Opens T, IsSharp (T.presheaf.obj (op U))`. |
| The nonidentity germs form prime ideals m_x | `h x : MonoidPrime P` and its exact carrier equality with `{p : P \| germ ... (φ p) ≠ 1}`. The dependency's `MonoidPrime` contains the ideal, properness, and complement-closure conditions and allows the empty ideal. |
| The prime map is continuous | `h : T.carrier ⟶ TopCat.of (MonoidPrime P)` is a continuous map in TopCat, fixed pointwise by its prime carriers. |
| The opens V_a are the identity-germ loci | `V : P → Opens T` with `(V a : Set T) = {x : T \| germ ... (φ a) = 1}`. |
| h inverse image D(a) equals V_a | `V a = (Opens.map h).obj (basicOpen a)`. |
| φ(a) restricts to zero | `T.presheaf.map (homOfLE le_top).op (φ a) = (1 : T.presheaf.obj (op (V a)))`. |
| A homomorphism from P_a | `lam a : Algebra.faceLocalization P (Submonoid.powers a) →* T.presheaf.obj (op (V a))`. |
| Formula on p-na | For every `p`, `n`, and localization element `q` with `q.val = of p * (of a ^ n)⁻¹`, `lam a q` is the restriction of `φ p`. In particular n=0 is precisely extension of the numerator map. No arbitrary fraction representative is chosen. |
| The extension is unique | Every monoid homomorphism `μ` agreeing on all numerator elements (`q.val = of p`) equals `lam a`. This tests the extension property alone, rather than assuming the whole fraction formula for a competitor. |
| The lift kills localization units | `∀ a q, IsUnit q → lam a q = 1`. |
| Descent to sharpening | `θ a : Associates (faceLocalization P (powers a)) →* ...` and `θ a (Associates.mk q) = lam a q` for every q. The quotient map is surjective, so this determines the descended map uniquely. |
| Compatibility for every D(b) subset D(a) | For every `basicOpen b ≤ basicOpen a`, there is the inclusion `i : V b ⟶ V a`, and for every q and r with the same ambient completion value, `T.presheaf.map i.op (θ a (Associates.mk q)) = θ b (Associates.mk r)`. |
| Overlap is D(a+b) and the two maps agree there | Final conjunct gives `basicOpen (a*b) = basicOpen a ⊓ basicOpen b` and `V (a*b) = V a ⊓ V b`, with both restriction equations through `θ (a*b)` for all representatives in the two chart localizations. |

The restriction clauses use the concrete representative description of the canonical
section identifications in `affineFan_localization_sections`: its restriction clause
says precisely that the image of `Associates.mk q` is `Associates.mk r` with
`r.val = q.val`. The theorem here states the commuting square on all such q and r;
it does not introduce an arbitrary localization map or arbitrary section equivalence.
Every quotient section has a representative q. The dependency guarantees the
corresponding r for each basic inclusion. Thus these pointwise equations are exactly
the square under the dependency's canonical identifications. On the overlap the
two source chart sections are localized to the common chart, and each equation
identifies its restriction with the same `θ (a*b)` applied to that localized class.
The inclusion morphisms are unique since Opens is a partial-order category.

Dependency interfaces read:

- `Sheaf.AlgebraicGeometry.FineFanBlowup`: `FineFan.IsFine`, `IsSharp`,
  `MonoidPrime`, `spectrumTopology`, `basicOpen`, `stalk`, and `germ`, including
  their full definitions and docstrings. `Algebra.faceLocalization` is its imported
  localization inside `Algebra.GrothendieckGroup`, defined in
  `Sheaf.TraceFormula.FaceLocalizationFs`. It is used directly, never redefined.
- `Sheaf.AlgebraicGeometry.AffineFanLocalizationSections`:
  `FineFan.affineFan_localization_sections`, including its numerator, restriction,
  germ, and zero-germ clauses and proof docstring. The current server source was
  also read through `scompile.py --source`; it agrees with the available local source.
  Both statement dependencies are public imports. These are also all proof dependencies.

Edge cases checked before writing: T may be empty; the first conjunct includes
U=empty, where the empty-cover sheaf axiom forces the section monoid to be a
singleton. P may be the trivial monoid. The prime carrier may be empty. With
a=1 (additively zero), V_a is all of T, and the formula for every n reduces to the
numerator formula. With n=0 it is the extension property on every basic chart.
Disjoint V_a,V_b are allowed: overlap restrictions land in sections on the empty
open. No nonemptiness, saturation, torsion-free condition, or finite affine cover
has been added. The universe u is arbitrary and follows the two dependency
interfaces for topological monoid sheaves and their actual stalks.

Searches performed for an existing statement:

- `msearch.py ... leanfinder`, query “A homomorphism from a fine sharp monoid to
  global sections of a sheaf with sharp stalks induces a continuous map to its
  monoid spectrum and compatible maps on sharpened localizations”: 8 hits, all
  ringed-space Gamma-Spec constructions, including `LocallyRingedSpace.toΓSpec`,
  `toΓSpecCApp`, and their basic-open formulas. Their signatures require rings and
  locally ringed spaces; they do not state this monoid-sheaf assertion.
- `msearch.py ... loogle '"MonoidSpectrum"'`: 0 hits.
- `msearch.py ... grep 'MonoidSpectrum|sharp.*stalk|sharpening'`: 0 hits.
- `rg` in `lean/WeilConjectures` for the item id: no match. Searched upstream and
  `lean/Sheaf` for `zeroGerm`, `sharpSection`, `MonoidPrime`, `faceLocalization`,
  and related section/germ patterns. Found the recorded FineFan framework and
  the affine universal-property theorem. The latter bundles a complete local
  sheafed-space morphism and its naturality, rather than the present chart-data
  lemma; no exact existing statement was found. Searched `dag/lean_names_upstream.json`
  for `MonoidPrime`, `IsSharp`, and the proposed theorem name: no match.

No statement correction or disputed statement is needed. No new nodes or dependency
repairs are required. Validation uses only the prescribed single-file server wrapper.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
