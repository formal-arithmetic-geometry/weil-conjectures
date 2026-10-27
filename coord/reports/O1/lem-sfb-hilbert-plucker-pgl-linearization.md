## Worker report

The delivery states `AlgebraicGeometry.exists_hilbert_plucker_pgl_linearization` in
`Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization`. Its only postponed proof is this
one theorem. The other declarations contain actual definitions or structures describing
supplied data, not objects selected from an unproved existence claim. The original node's
statement and accepted proof are unchanged. Two statement dependencies are added: the new
general group-scheme linearization definition and the definition owner for the existing
projective-family section and restriction constructions. The uniform-section-bound theorem
remains a proof dependency only.

Source read: Morrison, *GIT Constructions of Moduli Spaces of Stable Curves and Maps*,
[arXiv:0810.2340](https://arxiv.org/pdf/0810.2340), §2.1, printed pp.4--5, especially the
paragraphs identifying the Hilbert quotient, Plücker embedding and determinant line. The
local source record explicitly says the PDF is wanted locally; the PDF was read online.
The arbitrary-characteristic central descent and stability clauses follow the eleven
accepted DAG proof steps, all reproduced in the theorem docstring. The current blueprint
reference tool reports no blueprint ancestor for this created input; the new node preserves
that null ancestor and the existing chain, with this item prepended to `via`.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Any field k | `(k : Type u) [Field k]`, after the existential bound M; there is no characteristic restriction. |
| r ≥ 2 | The parameter `n : ℕ` writes `r = n + 2`. Every allowed r has this form, including r = 2 at n = 0. Coordinates and matrix schemes use the same `ULift (Fin (n + 2))`. |
| Admissible Hilbert polynomial | `P : NumericalHilbertPolynomial` and `hP`, which explicitly asserts existence of a field, a projective closed immersion and its coordinate Hilbert polynomial P. The supplied `Field` structure in this existential is used explicitly, avoiding an auto-bound instance. Numerical polynomials are the dependency's integer-valued rational polynomials, not an extra realizability condition. |
| H is the Hilbert scheme of the recorded representability theorem | `D : Hilbert k n P`. Its `representation` is the dependency's literal `properHilbertPresheaf ... .RepresentableBy total`; `components`, `inclusion`, `coproduct`, `projective` and `component` are precisely the polynomial-component data of that theorem, specialized to the full projective ambient scheme. In particular the coproduct law is retained, so no extraneous multiple preimages can occur outside the polynomial locus. `D.H` is just `D.components P`. |
| Universal family f and hyperplane L | `D.ideal` is the universal ideal transported to projective space over `D.H.left`; `universal_ideal` fixes it to `(representation.homEquiv (inclusion P)).1.comap` along the canonical `ProjectiveSpace.isPullback_map ... .isoPullback.hom`. The family is its actual subscheme with structural map `subschemeι ≫ HilbertSectionBound.projection`. The restricted twist is the recorded `closedTwist`. |
| M(P,r) independent of k | The conclusion is `∃ M : ℕ, ∀ (k : Type u) [Field k] (D : Hilbert k n P) (m : ℕ), M ≤ m → ...`. Thus the bound precedes both the field and every representative. A natural bound suffices for the integer high-degree assertion; negative twists are never relevant after choosing a nonnegative bound. |
| f_*L^m locally free of rank P(m) | `sections D m` is the actual `HilbertSectionBound.closedSections`. In `Presentation`, `p`, `value` and `rank` assert P(m) = p and the recorded finite-locally-free rank p predicate. No natural-number truncation of a possibly negative evaluation is used. |
| Arbitrary base change of the direct image | `Presentation.base_change` is `IsIso` of the existing, adjoint-defined `Scheme.Modules.moduleBaseChangeMap`, for every scheme and every map to H, with the actual family fibre product and its pulled-back restricted twist. |
| Quotient of Sym^m(k^r) tensor O_H | `N` and `monomials` give an equivalence with all degree-m monomials, not a selected subset. `quotient` is the map on the standard free generators given by `monomialRestriction`; that section is obtained from the actual `polynomialMap ≫ sectionRestriction`. `surjective` is `Epi` of this fixed map. This is the monomial-basis realization of the constant symmetric-power module. |
| Resulting Grassmannian map | `grassmann`, `universal`, `universal_quotient`, `universal_surjective`, `universal_rank`, and `grassmann_classifies` give the quotient Grassmannian's universal-element property on every test scheme. The unique map with the quotient-preserving isomorphism is precisely the universal property in `exists_freeQuotientGrassmann_projective`. `hilbert_map` and `hilbert_quotient` require that this map classifies the fixed restriction quotient. |
| Plücker map and closed immersion | `plucker` has the dependency's p-element-subset projective coordinates, `plucker_closed` makes it closed, and `plucker_coordinates` fixes it by the ordered wedges of the universal quotient generators. `embedding` states that `hilbert_map.left ≫ plucker` is a closed immersion. The definition permits p = 0 and p = N; the coordinate type is a singleton in both cases. |
| Hyperplane line is det(f_*L^m) | `determinant D m p` is exactly `Scheme.Modules.exteriorSheaf (sections D m) p`. `hyperplane` identifies the pulled-back hyperplane with this line. `invertible` and `ample` give the asserted ample polarization; `power_invertible` and `power_ample` do so for its rth power. |
| PGL is the projective matrix group scheme | `G`, `π`, `roots`, and `cover` use the complete recorded `ProjectiveMatrixCentralCover.Presentation`. This includes the fpqc quotient universal property, scalar GL torsor, SL cover, full μ_r kernel, finite locally free rank r and geometric properties. It does not substitute the abstract group of k-valued matrices. |
| Changing projective coordinates gives the action on H | `action : ModObj G.X D.H` is Mathlib's internal algebraic action. `coordinate_automorphism`, `coordinate_over`, `coordinate_line` and `coordinate_formula` specify the actual projective matrix automorphism by its linear homogeneous-coordinate formula. `entry` pulls back the existing matrix-coordinate functions on arbitrary test schemes. `coordinate_action` says the universal ideal of the translated Hilbert point is its inverse-image ideal under the inverse projective automorphism. Thus an arbitrary action cannot satisfy the presentation. |
| Natural SL action linearizes the determinant | `sl_action` is an internal action of the existing SL scheme and `sl_restriction` fixes it as the restriction along inclusion followed by π. `sl_line` is a genuine linearization on the determinant. `determinant_formula` fixes its maps on all generating monomial wedges by the coefficients of the degree-m inverse-coordinate substitution. The `coefficient` definition constructs those coefficients as an actual multivariate polynomial; it is not an arbitrary representation. |
| Linearization means a linear total-line action over the base action | The new `GroupSchemeLinearization.Linearization` gives O_T-linear pullback isomorphisms on every test scheme, with unit, multiplication and pullback cocycles. Naturality on all tests is precisely algebraicity, and evaluation on the universal group times base recovers the total-line action. No geometric-point-only linearization is used. |
| A_m = Λ_m^r has PGL linearization restricting to the induced power | `pgl_line` is a linearization on the literal `determinant ... .tensorPow (n + 2)`. `descent` equates its restriction, via `HEq` only to account for the equal base-action maps, with `sl_line.powerLift ... (n + 2)`. `powerLift` uses the existing canonical monoidal pullback and tensor-power isomorphisms, not an independently chosen power linearization. |
| Geometric semistable and stable loci agree | `semistable_points` and `stable_points` assert both membership in the specified open and the SL/PGL equivalence, for every algebraically closed extension and every point. `IsSemistable` means a positive-degree invariant section is nonzero; invariance is equality of pullbacks on all test schemes. This uses the existing PGL API convention of sections over the base field. The accepted flat-base-change invariant-kernel argument identifies this with sections over the geometric field. |
| Closed orbit in the semistable locus | `Linearization.IsStable` requires a closed subset of the actual Ω-base change whose semistable Ω-points are exactly the orbit. On the finite-type schemes here this is exactly relative closedness in the semistable open. The orbit is taken using every Ω-point of the group scheme. |
| Scheme-theoretic stabilizer dimension zero | `stabilizer` is the equalizer of the orbit map and the constant map on G × Spec Ω in schemes; `topologicalKrullDim ... = 0` is required. The equalizer retains nilpotents. No tangent-space dimension or reducedness assumption is substituted. |
| Loci are open subschemes | `semistable` and `stable` are actual `D.H.left.Opens`; the point equivalences characterize the corresponding open subschemes. |
| Formation commutes with any field extension | For each K/k the theorem supplies `DK`, `EK`, and the Hilbert comparison `h`; `IsPullback h ... (extension k K)` identifies the actual Hilbert base change, and the next equality identifies its actual universal ideal. The final equalities are `EK.semistable = h ⁻¹ᵁ E.semistable` and `EK.stable = h ⁻¹ᵁ E.stable`. Both packages carry the same coordinate and determinant normalizations. |
| Every characteristic, including nonreduced μ_r | No invertibility-of-r or characteristic hypothesis occurs. `cover` is the full group-scheme central-cover presentation; `descent` and every linearization equation quantify over all test schemes. The determinant convention is contragredient: a scalar t acts on sections by t^(-m) and on the determinant by t^(-mp). On the rth power it acts by t^(-rmp), which is 1 in the full ring k[t]/(t^r-1), including when it is nonreduced. |

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.ProjectiveHilbertPolynomialRepresentability`:
  `exists_projective_hilbert_polynomial_representation`, including its full signature and
  nine-step docstring. Its public dependencies supply `properHilbertPresheaf`,
  `NumericalHilbertPolynomial` and `HasProjectiveFibreHilbertPolynomial`.
- `Sheaf.AlgebraicGeometry.FreeQuotientGrassmannProjective`:
  `exists_freeQuotientGrassmann_projective` and `freeQuotientPullback`, including their
  universal-element, generator and Plücker normalizations.
- `Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover`:
  `ProjectiveMatrixCentralCover.Presentation`, `extension`, and `exists_presentation`;
  the actual GL, SL and roots schemes come from its recorded dependencies.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`;
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`;
  `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`: `exteriorSheaf`, `exteriorSheafSection`
  and the rank-zero normalization in `exteriorSheaf_zero_iso`.
- `Sheaf.AlgebraicGeometry.HilbertUniformSectionBound`: `closedSections`, `closedTwist`,
  `projection`, `polynomialMap`, and `sectionRestriction`, now owned for statement purposes
  by `def-sfb-projective-closed-family-sections`. The theorem `exists_uniform_bound` is
  a proof input only, not a construction used in the signature.
- The new generic interface reuses `PGLLinearization.fieldTest`, `geometricImage`,
  `powerIso`, `pullbackPowerIso`, `pullbackΓ` and the canonical sheaf pullback comparisons
  from `Sheaf.AlgebraicGeometry.PGLLinearizedPolarization`; it does not copy these maps.
  Internal group actions and their group laws are Mathlib's `Grp` and `ModObj`.
- All already recorded proof-dependency modules are imported privately, except modules
  needed by the signature, which are public. The affine PGL quotient orbit-topology
  proof node currently has no Lean record, so it contributes no import. No proof or
  auxiliary theorem for that unstated proof input is added in stage 2.

Edge cases checked before and during the statement reading:

1. r = 2 is n = 0, with two homogeneous coordinates; no extra lower bound was added.
2. P = 0 (the empty embedded subscheme) has p = 0, the empty wedge and the structure
   determinant line. The rank-zero Grassmannian and Plücker target are points. The
   determinant-action formula uses the singleton type of empty tuples, hence gives
   the identity rather than an empty sum. Semistability is all of that Hilbert point;
   stability is empty because the whole positive-dimensional group stabilizes it.
3. The full projective-space polynomial has p = N. The Grassmannian and Plücker target
   again have one point; there is no strict-rank inequality in the statement.
4. Nonreduced test schemes occur in the quotient classification, matrix automorphism,
   universal-ideal equation and every linearization/invariance equation.
5. In characteristic dividing r, the equalizer and μ_r are not reduced. Scheme dimension
   still admits finite nonreduced stabilizers; tangent-space dimension is never used.
6. Every field extension is allowed, including the identity, inseparable extensions
   and extensions of algebraically closed fields. Every scheme map is allowed in the
   direct-image base-change clause. Empty test schemes are retained.
7. The supplied representative is constrained by the full coproduct representation,
   not just an iff with unique factorization for a single index. This prevents spurious
   components from creating a vacuous or false premise.
8. Matrix and quotient coordinates are normalized, so a trivial action on an arbitrary
   Hilbert component or a different character on the determinant cannot replace the
   specified coordinate action and determinant linearization.

Searches actually run:

- `msearch.py leanfinder`, query `Hilbert scheme Plucker embedding determinant line bundle SL linearization PGL descent`:
  eight hits, including the module Grassmannian and general Proj morphisms; no Hilbert
  scheme embedding or determinant-linearization theorem.
- `msearch.py loogle`, query `AlgebraicGeometry, Hilbert`: no hits, unknown identifier
  `AlgebraicGeometry`; this search alone was not treated as evidence of absence.
- `msearch.py grep`, query `HilbertScheme|Plucker|Linearization|Semistable`, restricted to
  Mathlib/AlgebraicGeometry: zero hits.
- The three general-linearization searches are recorded verbatim by query and result
  digest in the new node; see the next section.
- `rg`/`grep` in both `lean/WeilConjectures` and `lean/Sheaf`, by the item id and by
  linearization, invariant/semistable/stable, Hilbert and determinant terminology.
  There is no existing theorem for this item. `PGLLinearizedPolarization` is PGL-specific;
  `TrivialTorusCoherentData.Linearization` only permits a trivial base action;
  `HopfActionModuleData.Linearization` is affine ring/module descent data. None gives a
  general moving-base group-scheme linearization with the full stabilizer definition.
- A parsed search of definition-node statements across `dag/nodes` confirmed these
  existing definitions and no general equivalent. `blueprint_refs.py search
  'group scheme linearization'` returned zero blueprint matches; searches for
  `linearization` and `linearized` did not yield this notion. The ancestor command
  reported that this created node has no blueprint ancestor.

No statement correction and no STATEMENT-DISPUTED flag. Both delivered modules compile
through `scompile.py`, individually in dependency order, with no unexpected warning.
The first compiler failures were repaired: a reserved identifier was renamed, the SL
bundle uses the actual `Grp` constructor, the scheme category is explicit in the
geometric fibre product, and monomial restrictions now use `freeHomEquiv` on the actual
polynomial restriction map, avoiding an expensive conversion of global sections of a
pushforward. No timeout limit or launcher tool was changed.

## New nodes

`def-sfb-group-scheme-linearization` records the general linearization and geometric
stability notions required simultaneously for the existing SL and PGL schemes. Its
module is `Sheaf.AlgebraicGeometry.GroupSchemeLinearization`. It uses Mathlib's actual
internal group action, actual pulled-back module isomorphisms with their three cocycles,
and the existing monoidal power comparisons. Its full scheme-theoretic stabilizer is
constructed as a scheme equalizer. There are no postponed theorems in this module.

Source: Morrison §2.1, lifting the group action to the line; the cocycle and stability
notions explicitly spelled out in the item's accepted statement. The node cites the
existing general field, scheme, group, sheaf, pullback, fibre-product, dimension and
PGL tensor-power interfaces. It creates no second definition of those objects.

Actual semantic searches were `leansearch` with query `linearization of an invertible
sheaf for a group scheme action` (eight representation-theory linearization hits),
`leanfinder` with query `group scheme action linearization invertible sheaf semistable
stable locus` (eight hits on representations, invariants and local module sections), and
`grep` with query `structure.*Linearization|def.*IsSemistable|def.*IsStable` in
Mathlib/AlgebraicGeometry (five unrelated stable-under-base-change morphism-property hits).
All three were successful searches; none was an exact match. DAG, blueprint and both
project source trees were also searched as described above. The PGL-specific and
trivial-base definitions were opened before deciding that this new node was needed.

The first dry-run preflight requested the standard `import_flags` key on the new
definition node. It is supplied as an empty list; no mathematical field changed.


`def-sfb-projective-closed-family-sections` is the H2 repair requested by L for immutable
head `32f640a8113f`. It owns ten existing plain definitions in the unchanged module
`Sheaf.AlgebraicGeometry.HilbertUniformSectionBound`, with `lean.existing: true`.
Its self-contained statement introduces every scheme, twist, direct image, free monomial
module, and canonical map. In particular, the five constructions directly used by the
item (`closedSections`, `closedTwist`, `projection`, `polynomialMap`, `sectionRestriction`)
are all explicitly listed. The item cites this definition node instead of
`lem-sfb-hilbert-uniform-section-bound` in `stmt_deps`; the latter remains in `proof_deps`.
This follows the existing definition-owner precedent
`def-sfb-projective-coordinate-hilbert-polynomial`. No source module is edited or copied.

The new node's clauses match the existing declarations as follows: the standard ambient
twist and projection are `twist` and `projection`; restricted twist is `closedTwist`;
ambient and family direct images are `polynomialSections` and `closedSections`; the
adjunction-unit restriction is `sectionRestriction`; the free monomial sheaf is
`polynomialModule`; integral homogeneous monomials and their pulled-back sections are
`integralMonomial` and `monomialSection`; the basis-defined map is `polynomialMap`.
All are definitions with actual data. They are defined for arbitrary morphisms, so the
node imposes no closed-immersion or other assumption absent from their signatures.
Integer twists include negative degree; monomial maps use natural degree only. The
cases n = 0, d = 0, empty base and empty family are retained by those constructions.
The new node asserts no theorem about their ranks, surjectivity or base change.

Searches for the ownership repair: LeanSearch queried canonical homogeneous polynomial
restriction and direct-image sections of twists of a closed relative projective family
(eight hits on Proj section maps and homogeneous components); LeanFinder queried the
canonical map from homogeneous polynomials to O(d) sections on a closed projective
subscheme (eight Proj/localization-map hits); Mathlib grep for
`closedSections|polynomialSections|sectionRestriction|polynomialMap` in AlgebraicGeometry
returned zero hits. Their exact logged results are in the new node. Project-source rg
found the desired definitions in HilbertUniformSectionBound and unrelated restriction
maps upstream. DAG rg found only the uniform-bound theorem record, not a definition
owner; blueprint search 'projective closed family sections' returned zero nodes.
The local Stacks text read was coherent.tex around
`lemma-cohomology-projective-space-over-ring` (01XT), including the monomial-basis notation,
and constructions.tex `definition-projective-space`.

## Repair self-check by O1

Compared the saved packet with current shared main: only the item's `lean` and added
`stmt_deps` differ; the accepted statement, all eleven proof steps and `proof_deps` agree.
The saved pre-repair packet passed deliver2.py --no-push at commit `46d41b064eb`.
The substantive repair is the new definition owner and replacement of the erroneous
statement dependency; the theorem and both delivered Lean files are retained unchanged.
The required statement-dependency definitions are now distinct from the uniform-bound
proof input. This addresses the sole mandatory return point; the mathematical statement
was independently accepted by L and has not changed. No statement correction is made.

Repair validation: `scompile.py` compiled both retained modules in dependency order with
no errors or unexpected warnings. The repaired packet passed the server preflight and
all per-file compiles with `deliver2.py --no-push` at commit `7d228546e23`.
A final field-by-field check against current shared main confirms that only `lean` and
the two new definition dependencies differ in the item's node; its statement and proof
are byte-identical. The new existing signature is verbatim from the published module.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
