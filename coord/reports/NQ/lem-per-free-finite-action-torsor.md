## Worker report

Item: lem-per-free-finite-action-torsor. Module:
`Sheaf.AlgebraicGeometry.FreeFiniteActionTorsor`, declaration
`AlgebraicGeometry.free_finite_action_torsor`. Its proof is `sorry`, as required
for stage 2. The only helper is the fully defined proposition
`AlgebraicGeometry.Scheme.Hom.HasGaloisFunctionFieldAction`, packaging the
function-field clause of this same node. It introduces no new carrier, field
map, or action construction, and is listed in lean.declarations.

Source read: ILO, Travaux de Gabber, Expose IX 1.4, printed pp. 132--133
(PDF pages 138--139), particularly situation (*), identifying the open with
its inverse image and asserting the etale Galois cover with the given group.
The node's ten-step proof is reproduced in the theorem docstring.

Hypothesis correspondence:

- Finite group acting on C: `{G : Type v} [Group G] [Finite G]` and
  `a : G →* Aut C`. Mathlib's Aut multiplication is reverse categorical
  composition, hence this is the left action in the node.
- Integral excellent Noetherian C: `[IsIntegral C] [IsNoetherian C]`, and
  `_hexc : ∀ W : C.affineOpens, IsExcellent Γ(C, W)`. Excellence is tested
  on every affine coordinate ring, using the recorded excellent-ring notion.
- Admissibility: the first conjunct of
  `_hquotient : IsAdmissibleFiniteSchemeQuotient a q` says that every orbit
  is contained in an affine open. This is precisely the node's convention.
- Dense stable open: `U : C.Opens`, `_hdense : Dense (U : Set C)`, and
  `_hstable : ∀ g c, c ∈ U → (a g).hom c ∈ U`. Applying the latter to
  inverses gives stability in both directions, without assuming a separate
  action on U.
- Freeness on geometric points: `_hfree` quantifies over all algebraically
  closed fields Ω and all maps `Spec Ω ⟶ U.toScheme`. Its equation compares
  `x ≫ U.ι ≫ (a g).hom` with `x ≫ U.ι`, and concludes `g = 1`.
- The existing scheme quotient with invariant structure sheaf and finite q:
  `q : C ⟶ Y` and `_hquotient` use the already landed quotient definition.
  Its remaining conjuncts are IsFinite q, action invariance, orbit quotient
  topology and ordinary orbit fibres, and the canonical injective section map
  with image exactly invariant sections. These are the meaning of the scheme
  quotient C/G, not an assumption that the action is free, flat, etale or a
  torsor. The node explicitly defines the invariant-sheaf convention.
- Noetherian C/G: `[IsNoetherian Y]`. Y is the specified quotient scheme,
  rather than a separately chosen quotient construction.

Conclusion correspondence:

- V = q(U) and V open: `∃ V : Y.Opens, (V : Set Y) = q '' (U : Set C)`.
  The type of V supplies openness; the equality fixes its underlying subset.
- U is the full inverse image: `q ⁻¹ᵁ V = U`.
- U = C ×_Y V with the given inclusions: the map
  `p : U.toScheme ⟶ V.toScheme` and `IsPullback U.ι p q V.ι` specify the
  commuting square and its complete universal property. This is equivalent
  to an isomorphism with Mathlib's chosen pullback, preserving projections.
- Finite etale restriction: `IsFinite p ∧ Etale p`.
- The action on U is the given action restricted: `aU : G →* Aut U.toScheme`
  and `(aU g).hom ≫ U.ι = U.ι ≫ (a g).hom`. These equations determine the
  restriction, so no arbitrary new action is substituted.
- Orbit-space quotient: `IsAdmissibleFiniteSchemeQuotient aU p` supplies
  the quotient topology, ordinary orbit fibres and invariant structure sheaf.
  Admissibility on U follows because p is finite and an orbit is contained in
  the inverse image of an affine neighbourhood of its image.
- Torsor and simple transitivity on every geometric fibre: the existing
  `t : Scheme.GaloisCoverAction G V.toScheme` supplies finiteness, etaleness,
  surjectivity, simple transitivity and the scheme quotient universal property.
  `e : t.Z ≅ U.toScheme`, `e.hom ≫ p = t.π`, and
  `t.smul g ≫ e.hom = e.hom ≫ (aU g).hom` identify its actual total space,
  morphism and action with the ones in this node. There is no bare existence
  of an unrelated torsor or map.
- The separated conditional: `C.IsSeparated → ...`; density of U is already
  a hypothesis, as in the node. The first conjunct is `Dense (V : Set Y)`.
- The function fields are meaningful: `∃ hY : IsIntegral Y` supplies the
  integrality of the quotient implicit in the node's notation k(C/G).
- The induced function-field extension: the helper requires
  `hη : q (genericPoint C) = genericPoint Y`. Mathlib's functionField is the
  stalk at the generic point. `q.functionFieldMap hη` is the existing generic
  stalk map from DivisorPullback, with the stalk transport along hη. The helper
  quantifies over algebra structures whose algebraMap equals precisely that
  ring homomorphism. This quantification is not vacuous: its `toAlgebra`
  structure always exists, and any such algebra structure has the same map.
- Galois with group G: the helper states IsGalois, FiniteDimensional and
  `ρ : G ≃* (C.functionField ≃ₐ[Y.functionField] C.functionField)`. For each
  g it requires that ρ(g) is exactly the generic stalk pullback of a(g⁻¹),
  including the proof that the action preserves the generic point. This pins
  the group identification to the induced action, with the inverse required
  by contravariance. It does not merely assert an abstract group isomorphism.

Dependency declarations used (full declarations and docstrings read):

- def-pc-integral-scheme: Mathlib.AlgebraicGeometry.Properties,
  AlgebraicGeometry.IsIntegral.
- def-exc-excellent-ring: Sheaf.RingTheory.ExcellentRing, IsExcellent.
- def-weil-pbc-noetherian-ring: Mathlib.RingTheory.Noetherian.Defs,
  IsNoetherianRing; scheme form AlgebraicGeometry.IsNoetherian in
  Mathlib.AlgebraicGeometry.Noetherian.
- def-weil-finite-integral-morphism: Mathlib.AlgebraicGeometry.Morphisms.Finite,
  AlgebraicGeometry.IsFinite (also supplied by the quotient definition).
- def-weil-etale-morphism: Mathlib.AlgebraicGeometry.Morphisms.Etale,
  AlgebraicGeometry.Etale.
- def-sbc-normal-dominant-galois: Sheaf.AlgebraicGeometry.NormalScheme,
  AlgebraicGeometry.Scheme.GaloisCoverAction, including every field of its
  signature. This unrestricted-group form avoids changing the group universe.
- def-weil-geometric-point: Mathlib.FieldTheory.IsAlgClosed.Basic, IsAlgClosed,
  and Mathlib's Spec-field morphism convention (SpecToEquivOfField read).
- def-pc-fibre-product: Mathlib's pullback universal property, expressed by
  CategoryTheory.IsPullback from the scheme pullback imports.
- def-weil-proper-morphism: Mathlib.AlgebraicGeometry.Morphisms.Proper and
  Separated, AlgebraicGeometry.IsSeparated / Scheme.IsSeparated.
- def-sc-generic-point: Mathlib.Topology.Sober, genericPoint and its
  IsGenericPoint specification.
- def-weil-pbc-module-stalk: recorded upstream
  WeilConjectures.Topology.PresheafModuleStalkFunctor (read through
  scompile.py --source); stalk carriers are Mathlib's presheaf stalks.
  Scheme.functionField and Scheme.Hom.functionFieldMap use those same
  structure-sheaf stalks; no second function-field carrier is defined.
- Added existing landed dependency def-per-admissible-finite-scheme-quotient:
  Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient,
  AlgebraicGeometry.IsAdmissibleFiniteSchemeQuotient. Read its entire
  definition and node. The item gains only this stmt_dep and its lean record;
  no natural-language statement or proof is changed.

The helper also uses the existing Scheme.functionField from
Mathlib.AlgebraicGeometry.FunctionField; Scheme.Hom.functionFieldMap from
WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback; and IsGalois from
Mathlib.FieldTheory.Galois.Basic. The current published DivisorPullback source
was checked with scompile.py --source. All already stated proof dependencies
are reached by the imports: affine groupoid orbit fibres, finite-flat affine
relation quotient, finite-morphism permanence and closedness, geometric points
and algebraic closures, fpqc descent, unramified morphisms, affine function-field
fraction rings, finite field action/fixed-degree, and finite Galois fixed fields.

Edge cases checked: C cannot be empty because IsIntegral includes Nonempty.
A dense open in integral C is nonempty, so the free hypothesis forces the
induced action to be faithful even at the geometric generic point. The empty
boundary U = C and the trivial group are both allowed. Nonfaithful actions
are not independently excluded: freeness supplies the necessary faithfulness.
All characteristics, including those dividing |G|, are allowed: free constant
finite-group actions remain etale, with no averaging assumption. C need not
be separated for the torsor assertion; separatedness is used only as the
conditional requested for the final clause. Y is not assumed integral in the
hypotheses. U need not be affine or quasi-projective. The group universe v is
independent of the scheme universe u; geometric points use the same universe
as the recorded dependency, sufficient for algebraic closures of residue
fields and simple-transitivity testing.

Searches performed:

- msearch.py leanfinder: "A finite group acting freely on a scheme has a finite
  etale torsor quotient". Eight hits, abstract Galois-category actions and
  set-action orbit results; no scheme quotient theorem matching the item.
- msearch.py loogle: `"GaloisCover", "torsor", "Quotient"`. Zero hits.
- msearch.py grep in AlgebraicGeometry:
  `(admissible|invariant|free).*(action|quotient)|GaloisCover`. Zero hits.
- msearch.py leansearch: "finite group free action scheme quotient finite
  etale torsor function fields Galois". Eight hits: set-action orbit splittings,
  IsGalois.of_fixed_field, IsGaloisGroup.fixedPoints and FixedPoints.finrank_eq_card.
  These supply ingredients but not the scheme theorem.
- Direct rg searches of upstream WeilConjectures and side lean/Sheaf for
  GaloisCoverAction, GaloisCover, admissibility, invariant sheaves, quotient
  actions and function-field maps. Found NormalScheme's existing torsor
  definition and the landed AdmissibleFiniteSchemeQuotient, both reused.
  Upstream EtaleTorsor and EtaleTorsorSpreading have torsor definitions and
  spreading results, not this free-locus theorem.
- Direct rg for the exact item id in upstream WeilConjectures: no hits.
- Direct rg for the proposed names HasGaloisFunctionFieldAction and
  free_finite_action_torsor in dag/lean_names_upstream.json, Mathlib,
  upstream WeilConjectures and side lean/Sheaf: no hits before writing.

No statement dispute, source-based correction, new DAG node, or dependency
repair was needed. The owning helper is the node's explicit function-field
clause, not an independent missing notion. Its proposition is written in full.

Validation: scompile.py compiled both sandbox and library module forms cleanly
with autoImplicit disabled, in approximately three seconds each. The final
module is also compiled through the prescribed delivery dry run.

## Second reading by NQ

Reread the node and final module side by side. The first draft wrote the
quotient conditions inline. The second pass found the already landed
IsAdmissibleFiniteSchemeQuotient and replaced those copies by that definition,
adding its existing node to stmt_deps. Also checked that the restricted action
and torsor are pinned to U and p, and that the Galois-group isomorphism is the
inverse pullback of the original action. Both canonical compatibility checks
are explicit equations in the final signature. Checked each hypothesis and
conclusion against the correspondence above; no missing clauses or additional
geometric assumptions were found. Every theorem proof remains only `sorry`.

This is the dispatched worker's second reading, not a claim that another agent
performed an independent review. The dispatcher explicitly forbids starting
other agents; the maintainer's independent delivery review is still required.
