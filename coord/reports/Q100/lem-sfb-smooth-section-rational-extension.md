## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothSectionRationalExtension` states
`AlgebraicGeometry.smooth_section_rational_extension`, with its entire proof `sorry`.
There are no definitions, extra nodes, dependency repairs or statement corrections.
The item node changes only in `lean`.

Hypothesis and conclusion correspondence:

- The four schemes are `{B T X Y : Scheme.{u}}`; the arbitrary explicit universe
  covers schemes of any size in the project's category of schemes.
- T has a finite Noetherian affine cover: `[IsNoetherian T]`. Mathlib's
  `isNoetherian_iff_of_finite_iSup_eq_top` in `Mathlib.AlgebraicGeometry.Noetherian`
  states precisely the finite affine cover equivalence. This does not assume T separated.
- Every local ring is an integrally closed domain: `hnormal` quantifies over all
  `z : T` and conjoins `IsDomain (T.presheaf.stalk z)` and
  `IsIntegrallyClosed (T.presheaf.stalk z)`. No integrality of the whole scheme is added.
  The existing `IsNormalScheme` in `WeilConjectures.AlgebraicGeometry.NormalScheme`
  additionally requires `IsIntegral`, so is inappropriate for this disconnected/empty case.
- The structural morphisms are `t : T ⟶ B`, `r : Y ⟶ B`, and `[IsSeparated r]`.
  `IsSeparated` is defined by `IsClosedImmersion (pullback.diagonal r)`, exactly the
  node's relative separatedness; no absolute separatedness of Y is imposed.
- The smooth morphism and section are `q : X ⟶ T`, `[Smooth q]`, `a : T ⟶ X`,
  and `ha : a ≫ q = 𝟙 T`. Categorical composition has the opposite written order
  from the node's function-composition notation.
- The dense open subscheme is `D : X.Opens` with `hD : Dense (D : Set X)`.
  Its morphism is `v : D.toScheme ⟶ Y`. The equation
  `hv : v ≫ r = D.ι ≫ q ≫ t` says it is a B-morphism for X's stated structure map.
- The second B-morphism is `b : T ⟶ Y` with `hb : b ≫ r = t`.
- T° is Mathlib's canonical open `a ⁻¹ᵁ D`, used directly rather than introducing a
  second notion. `hcodim` says every `z` with `ringKrullDim (T.presheaf.stalk z) ≤ 1`
  has `a z ∈ D`, exactly the condition z belongs to T°.
- The equality on T° is `hagrees : (a ∣_ D) ≫ v = (a ⁻¹ᵁ D).ι ≫ b`.
  Here `a ∣_ D` is the canonical scheme map from the preimage open into D;
  this is equality of scheme morphisms, including their structure-sheaf maps.
- The conclusion chooses an open `N : X.Opens` and a scheme morphism
  `w : N.toScheme ⟶ Y`. Its first conjunct `∀ z : T, a z ∈ N` says N contains a(T).
  Its second conjunct `w ≫ r = N.ι ≫ q ≫ t` states B-linearity. Its last conjunct
  restricts w and v by `X.homOfLE inf_le_left` and `X.homOfLE inf_le_right` from
  the literal intersection `N ⊓ D` and equates those scheme morphisms.
- No group structure on Y, quasi-compactness of X or Y, or separatedness of q is
  present. The conclusion adds no uniqueness requirement or equality outside N ∩ D.

Recorded statement dependencies used, with signatures and docstrings read:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom` (locally affine locally ringed spaces and their maps).
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, used through the exact diagonal definition of
  `AlgebraicGeometry.IsSeparated` in `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`. This is the affine-local smooth-ring-map notion identified
  with locally finitely presented formally smooth morphisms by Stacks 02H6.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim : (R : Type*) → [CommSemiring R] → WithBot ℕ∞`.

Other existing APIs used: `Scheme.Opens.toScheme`, `Scheme.Opens.ι`,
`morphismRestrict`, `Scheme.homOfLE` from `Mathlib.AlgebraicGeometry.Restrict`;
`IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`; Mathlib's existing ring
predicates `IsDomain` and `IsIntegrallyClosed`.

The proof docstring follows all seven node steps, including B₀-linearity and the
identification of the two section preimages in step 6. Proof imports include the
already stated normal-components theorem from
`Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents`, together with
Mathlib's relative separated equality, gluing, affine basis, open factorization,
affine compact/quasi-separatedness, Noetherian and smooth restriction modules.
The currently unstated proof nodes (smooth-normal-ascent, smooth-reduced-dense-pullback,
normal-affine-rational-indeterminacy, smooth-section-divisor-intersection) have no
recorded modules to import. No statement dependency is missing.

Edge cases checked: T empty makes X empty because q exists, and N can be empty.
For nonempty T, D empty is excluded by the codimension condition at generic points.
Disconnected normal T is retained by the stalkwise normality formulation. D = X
is allowed and v itself gives the conclusion. If every local ring of T has dimension
at most one, the section already lies in D and N = D is permitted. The dimension
bound is in `WithBot ℕ∞`, allowing dimension infinity and the conventional bottom
for the zero ring. Stalks at actual points are nonzero local rings. An empty Y
is allowed whenever the supplied maps exist. There are no extra finiteness or
separation assumptions on q, X or Y.

Searches:

- `msearch.py ... leanfinder`: "A rational map on a smooth scheme over a normal
  Noetherian base extends near a section if it agrees there with a morphism and
  is defined at all section points of codimension at most one". Eight hits:
  RationalMap and PartialMap interfaces, representative existence and field-map
  constructions; none asserts the extension in this node.
- `msearch.py ... leansearch`: "A rational map on a smooth scheme over a normal
  Noetherian base extends to an open neighbourhood of a section when it agrees
  there with a morphism and contains all points of local dimension at most one".
  Eight hits, all RationalMap/PartialMap definitions or over-base representatives;
  no matching theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.Scheme.RationalMap,
  AlgebraicGeometry.IsSmooth`. No hits; the service did not recognize IsSmooth.
  Local source confirms the current name is Smooth (IsSmooth is a deprecated alias).
- `msearch.py ... grep`: `smooth.*section|rational.*extension|section.*rational`
  under Mathlib/AlgebraicGeometry: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` with
  `smooth.*[Ss]ection|rational.*[Ee]xtension|section.*rational|smoothSection`:
  unrelated smooth coordinates, differential basis, purity and scalar extension
  declarations. Narrow follow-up in the AlgebraicGeometry directories with
  `smooth_section_rational_extension|rational.*section.*extend|smooth.*section.*extension`:
  no matching extension theorem. `grep -rn` of the item id in WeilConjectures: no hits.
- Read the BLR primary scan at
  https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
  PDF pages 115–116, printed pages 109–110. Its diagonal argument supplies the local
  affine-target boundary and section-intersection argument abstracted by this node.
  It is not the group-scheme theorem restated with a group hypothesis omitted.

No node fault or disputed statement found. The server wrapper `scompile.py Q100
lem-sfb-smooth-section-rational-extension <file>` passed in sandbox and library modes
(1.5 s and 1.7 s respectively). The proof remains `sorry`; nothing is proved in stage 2.

## Second reading by Q100

This dispatcher-assigned worker performed a separate rereading of the node and final
Lean signature; no other agent was started, as the brief forbids it. The maintainer's
independent review is still required. I checked each correspondence above against both
texts, especially the two structural-map equations, the genuine scheme-morphism equality
on T°, and the two canonical restrictions from N ⊓ D. All clauses match. I also checked
that the stalkwise normality permits disconnected T, the arbitrary universe is bound,
and every variable is explicitly bound. No change to the mathematical signature was
needed on this reading; only a docstring's stray leading space was removed.
