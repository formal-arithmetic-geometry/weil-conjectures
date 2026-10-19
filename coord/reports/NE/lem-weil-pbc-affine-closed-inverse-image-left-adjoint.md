## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint`
states `AlgebraicGeometry.Scheme.exists_affineClosedInverseImageLeftAdjoint`, with
one whole-proof `sorry` and no new definitions. Its source is Stacks Project,
proetale.tex, Tag 09BL, lemma-closed-immersion-affines-apply, clause (3).
I read the local source statement and its proof of (3), together with the DAG proof.
The five-step proof plan is in the theorem docstring.

Hypothesis and clause correspondence:

- Schemes Z and X: `{Z X : Scheme.{u}}`; `u` is explicitly declared.
- Affineness of both schemes: `[IsAffine Z] [IsAffine X]`.
- The given closed immersion: `(i : Z ⟶ X) [IsClosedImmersion i]`.
- The fixed small pro-etale sites: `ProEt.topology Z` and `ProEt.topology X`,
  on `Z.ProEt` and `X.ProEt`, with scheme universe u, site object universe u+1,
  site morphism universe u, and values `Type (u + 1)` as recorded by the dependencies.
- The ordinary inverse image: `proEtaleSheafInverseImage i (Type (u + 1))`,
  precisely the recorded left-Kan-extension/sheafification construction.
- Existence and direction of the extra functor: the existential `L` has domain
  `Sheaf (ProEt.topology Z) (Type (u + 1))` and codomain the X-sheaves.
- The required Hom bijections for every G and F, natural in both:
  `Nonempty (L ⊣ proEtaleSheafInverseImage i (Type (u + 1)))`.
  Mathlib's `Adjunction.homEquiv adj G F` has exactly
  `(L.obj G ⟶ F) ≃ (G ⟶ (proEtaleSheafInverseImage i _).obj F)`;
  its naturality lemmas cover morphisms in both arguments. Conversely a natural
  Hom equivalence constructs an adjunction by `Adjunction.mkOfHomEquiv`, so this
  encoding neither strengthens nor weakens the clause.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjective stalk maps).
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the recorded small-site
  convention; the set-valued part directly uses Mathlib's `Scheme.ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`; I read its full signature,
  docstring, body and ordinary inverse-image/direct-image adjunction.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: recorded sites/sheaves
  interface, in particular `CategoryTheory.Sheaf` (the full subcategory of sheaves).
- `Mathlib.CategoryTheory.Adjunction.Basic`: `CategoryTheory.Adjunction` and
  `CategoryTheory.Adjunction.homEquiv`.

Proof-only imports retain the recorded modules for the affine ind-etale basis,
closed-site functor properties, weakly contractible covers, lower-shriek criterion,
Yoneda, and dense-subsite comparison. Sheafification is already imported through
inverse image. The genuine proof prerequisite
`lem-weil-pbc-affine-closed-inverse-image-evaluation` has no Lean record in the
snapshot, so its import is omitted; it is not needed to type this statement.

Edge cases: empty Z, empty X (hence empty Z), identity closed immersions, and
nonreduced affines are all admitted. No nonemptiness, reducedness, Noetherianity,
choice of coefficient ring, site-universe equality, or arbitrary substitute inverse
image is imposed. Affine schemes are not restricted to chosen literal spectra.
The conclusion asserts only existence of the adjoint; it adds none of 09BL(5),(6).

Searches made:

- `msearch.py leanfinder`: “For a closed immersion of affine schemes the inverse
  image on pro etale sheaves of sets has a left adjoint”. Eight hits, chiefly
  module restriction/pushforward adjunctions, closed-immersion ideal-sheaf
  equivalence and etale forgetful full faithfulness; none is the extra set-sheaf adjoint.
- `msearch.py loogle`: `CategoryTheory.Adjunction, CategoryTheory.Functor.IsRightAdjoint`.
  Ten hits: generic adjunction interfaces and module/sheaf pullback adjunctions;
  no theorem about affine closed pro-etale inverse image.
- `msearch.py grep`: `proEtale.*[Aa]djoint|[Aa]djoint.*proEtale|closed.*[Ll]eftAdjoint`.
  Two unrelated cartesian closed category hits, no match.
- `rg` in the project Sheaf sources and upstream AlgebraicGeometry/ProEtale:
  `closed.*[Aa]dj|[Aa]dj.*closed|exists.*[Ll]eftAdjoint`.
  Existing closed-site lift adjunction is a different functor on affine site objects;
  no existing declaration of this sheaf inverse-image theorem.
- `rg` of the exact node id throughout upstream `WeilConjectures`: no hits.

No statement correction, new node, dependency repair, or disputed statement.

Validation: server-only single-file compile via scompile.py; delivery dry run via
`deliver2.py NE lem-weil-pbc-affine-closed-inverse-image-left-adjoint --no-push`.
The independent second reading is left to the next worker.


## Second reading by NE

I independently read the sandbox node and module, Stacks proetale.tex
lemma-closed-immersion-affines-apply (09BL), including its statement and proof
of (3), and the recorded statement-dependency declarations. The source assumes
only a closed immersion of affine schemes here. No ambient Noetherian,
separatedness, characteristic or nonemptiness hypothesis is present.

Object/hypothesis/conclusion checklist (all verdicts: exact):

1. Schemes Z and X: `{Z X : Scheme.{u}}`, with explicit `universe u`.
   I read Mathlib's `Scheme` structure and the def-pc-scheme record.
2. Both schemes affine: `[IsAffine Z] [IsAffine X]`. Mathlib's class says the
   canonical map to the spectrum of global sections is an isomorphism, so this
   covers arbitrary affine schemes, rather than just chosen spectra.
3. The specified morphism i is a closed immersion: `(i : Z ⟶ X)` and
   `[IsClosedImmersion i]`. I read the recorded class: a closed embedding with
   surjective stalk maps, exactly the node's geometric condition.
4. Small pro-etale sites in the fixed universes: `ProEt.topology Z` and
   `ProEt.topology X`. I read `Scheme.ProEt`, its precoverage and topology in
   Mathlib, and `ProEtaleDerivedCategory`. These are weakly etale schemes over
   the base with the pro-etale covering topology; objects have universe u+1,
   morphisms universe u, and the chosen set-valued sheaves use `Type (u + 1)`.
   No equality of the site object and morphism universes is imposed.
5. The ordinary inverse image: `proEtaleSheafInverseImage i (Type (u + 1))`.
   I read the actual dependency body: `proEtaleBaseChange` is the canonical
   weakly etale base-change functor, and inverse image is
   `Functor.sheafPullbackConstruction.sheafPullback`, the left Kan extension
   followed by sheafification. The direct-image adjunction is the ordinary
   continuous-functor adjunction. There is no arbitrary replacement functor.
6. The extra functor exists with the correct direction: `∃ L : Sheaf
   (ProEt.topology Z) (Type (u + 1)) ⥤ Sheaf (ProEt.topology X) (Type (u + 1))`.
   Mathlib's `Sheaf` is the full subcategory of sheaf presheaves, as required
   by def-weil-pbc-sites-and-cohomology; I read that definition and its record.
7. For every G and F, the specified natural Hom bijections:
   `Nonempty (L ⊣ proEtaleSheafInverseImage i (Type (u + 1)))`.
   I read `Adjunction`, `homEquiv`, the two naturality lemmas, and
   `mkOfHomEquiv`. Its component is precisely
   `(L.obj G ⟶ F) ≃ (G ⟶ (proEtaleSheafInverseImage i _).obj F)`.
   An adjunction supplies all components simultaneously, natural in both
   arguments; conversely those natural bijections construct an adjunction.
   Existential L precedes both Hom variables as the node requires. The
   conclusion does not include the distinct fully faithful/unit assertions
   of 09BL(5),(6), nor the abelian-sheaf adjoint of (4).

Edge cases: the empty scheme is affine and permitted for Z and X; an empty X
forces empty Z without requiring an extra hypothesis. Identity immersions,
nonreduced affines, all characteristics, and zero rings are admitted. There
is no index set, integer degree, coefficient module or zero-object binder to
restrict. Universe u is arbitrary, with precisely the recorded larger set
universe. No variable is unbound and no extra instance parameter is present.

Independent searches (using different wording from the first reader):

- LeanFinder: "Inverse image of set valued sheaves for affine closed immersions
  on the proetale site is a right adjoint" returned eight module restriction,
  pushforward and ideal-sheaf adjunction hits; none is this set-sheaf theorem.
- Loogle: `"Sheaf", "IsRightAdjoint"` returned twelve hits, including sheaf
  inclusion, sheaf/module pushforward and topological restriction interfaces;
  none asserts an extra adjoint for an affine closed pro-etale immersion.
- LeanSearch: "The inverse image on pro etale sheaves of sets along a closed
  immersion of affine schemes admits a left adjoint" was unavailable
  (Internal Server Error); this is not evidence of absence.
- `rg` over Mathlib, upstream WeilConjectures, project lean/Sheaf and the exact
  side framework lean/WeilConjectures used
  `pro.?etale.*(leftadjoint|rightadjoint)|closed.*inverseimage.*adj|inverseimage.*closed.*adj`.
  I opened the nearby upstream `upperStarLowerStarAdjunction` and
  `localizationLowerShriekAdjunction` in the finite-coefficient framework.
  The former is the usual inverse-image/direct-image adjunction; the latter
  requires a weakly etale localization map and is a different restriction
  functor. Neither is the affine closed-immersion theorem. The closed-site
  lift adjunction concerns site objects, not set-valued sheaves.

I also read the signatures of the imported affine basis equivalence,
`affine_closed_site_functor_properties`, `exists_weaklyContractible_cover`,
and `exists_leftAdjoint_of_covering_corepresentable_evaluations`. They support
the five numbered proof-plan steps; no new node or dependency module is being
delivered. The evaluation prerequisite has no declaration in this snapshot
and is correctly omitted as a proof-only import; it is unnecessary for typing
the statement. All available proof-dependency modules are imported, directly
or via the statement dependencies (including sheafification).

No mathematical mismatch, duplicate definition, hollow definition, proved
helper, or unrecorded correction was found. The module has one named theorem
with whole-proof `sorry`, source and blueprint docstrings, and the complete
five-step DAG proof plan. I left the correct Lean and node unchanged and
added this independent audit only. The node's lean.statement was checked
verbatim against the file's signature. The delivered module passed scompile.py
on the server with no errors or warnings (sandbox and library checks).
