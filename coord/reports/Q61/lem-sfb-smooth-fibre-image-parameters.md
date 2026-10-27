## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothFibreImageParameters` states
`AlgebraicGeometry.AlgebraicSpace.exists_regular_parameters_of_zero_dimensional_fibre`.
Its only postponed proof is this theorem, written `by sorry`. The declaration docstring
contains all six steps of the node's proof, including the local-ring quotient calculation,
spreading germs, and the final closed-point dimension argument. No definition is introduced.
The natural-language statement and accepted proof are unchanged.

Hypotheses, clause by clause:

- The base scheme is `{S : Scheme.{u}}`. The field over S is `(k : Type u) [Field k]`
  with `(sk : Spec (CommRingCat.of k) ⟶ S)`. All schemes and fields use the scheme
  universe; there is no smaller independent test universe.
- The scheme U/S is `(U : Over S)`; the point is `u₀ : U.left`. Its closedness is
  `hu₀ : IsClosed ({u₀} : Set U.left)`. There is no Noetherian, finite type, separated,
  or affine hypothesis on U or S.
- The algebraic space with its k-structure is `E : AlgebraicSpace S` and
  `q : E.obj.obj ⟶ yoneda.obj (Over.mk sk)`. Describing an algebraic space over k
  as its underlying S-space with this structure map is the usual relative convention.
  The map `hq` requires `Smooth (yoneda.preimage (a ≫ q)).left` for every scheme
  chart `a` with `IsEtale a`; neither a chosen atlas nor chart surjectivity is assumed
  in this test. These are the node's smoothness and etale-chart conventions.
- The S-morphism p is the natural transformation `p : E.obj.obj ⟶ yoneda.obj U`.
- The rational point is `z : yoneda.obj (Over.mk sk) ⟶ E.obj.obj`; its k-linearity
  is exactly `hz : z ≫ q = 𝟙 _`.
- The residue-field isomorphism and image condition are encoded by
  `e : Over.mk sk ≅ Over.mk (U.left.fromSpecResidueField u₀ ≫ U.hom)` and `he`.
  Contravariance of Spec makes `e.hom.left` the map Spec k → Spec κ(u₀).
  The equation `he` says p z is precisely this isomorphism followed by the canonical
  residue-point map. Thus u₀ is its image, and the induced κ(u₀) → k is an
  isomorphism. Conversely the node's induced residue isomorphism supplies this e;
  no arbitrary unrelated isomorphism or extension-field lift is substituted.
- The closed fibre is the actual presheaf pullback of p and the Yoneda image of
  the canonical Spec κ(u₀) → U over S. Its distinguished k-point is
  `Limits.pullback.lift z (yoneda.map e.hom) he`; both projections are prescribed.
  `hdim` asserts `etaleLocalDimension` at the point class of this lift is zero.
  This uses the existing definition whose scheme chart value is
  `topologicalKrullDimAt`, the infimum over open neighbourhoods. It does not use
  dimension of a stalk or dimension of the underlying quotient topology instead.

Conclusions, clause by clause:

- `∃ (O : U.left.Opens) (_ : IsAffineOpen O) (hu : u₀ ∈ O)` is an affine open
  neighbourhood U' of u. Sections on U' are written as global sections of O.toScheme,
  canonically the same regular functions as Γ(U,O).
- `fs : List Γ(O.toScheme, ⊤)` records the ordered functions f₁,...,f_d with
  the nonnegative integer d equal to `fs.length`. Every natural length is allowed;
  explicitly quantifying another d equal to the length would be redundant.
- The presheaf `Limits.pullback p (yoneda.map (Over.homMk O.ι rfl))` is p⁻¹(U').
  `V : Over S` and `a : yoneda.obj V ⟶ ...` give its scheme atlas. `IsEtale a`
  and `IsSurjective a` use the dependency's representable scheme-test definitions.
- The existential point `v : V.left` satisfies equality of its image point class in E
  with that of z. This is “above z” as a space point; a k-rational lift in the atlas
  is not required. Finite separable residue extensions are allowed.
- `RingTheory.Sequence.IsRegular (V.left.presheaf.stalk v)` applied to the mapped
  list asserts the exact regular-sequence conclusion. Each section is pulled to V by
  `(yoneda.preimage (a ≫ Limits.pullback.snd _ _)).left.appTop`, then mapped to
  the stalk by `V.left.presheaf.germ ⊤ v trivial`. This is the pullback germ, not a
  sequence in a different ring or the residue field.
- `∀ f ∈ fs, O.toScheme.Γevaluation ⟨u₀, hu⟩ f = 0` is vanishing at u.
- The existential ideal-sheaf datum J is constrained by the equality
  `J = Scheme.IdealSheafData.ofIdealTop (Ideal.ofList fs)`. Hence its `subscheme`
  is exactly V(f₁,...,f_d), with its scheme structure and possible nilpotents.
  This is a fully constructed Mathlib ideal sheaf, not an unspecified closed immersion.
- The pullback along `J.subschemeι ≫ O.ι` is E ×_U Z. The existential k-point
  `zJ` together with `zJ ≫ Limits.pullback.fst _ _ = z` asserts that the original
  rational point belongs to this fibre product. At its point class, the final
  `etaleLocalDimension ... = 0` is the last dimension conclusion of the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.Algebra.Field.Defs`: `Field` (the field dependency is a Mathlib leaf).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`, `IsSurjective`;
  their representability witnesses are genuine pullback squares over every test scheme.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and `.Basic` supply
  `Scheme.IdealSheafData.subscheme`, `subschemeι`, and `ofIdealTop`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `schemePointMap`, `Point`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleDimension`: `etaleLocalDimension`.
  The last two already-landed definition nodes are added to stmt_deps, as authorized
  by brief-stage2 §5. No new definition node or dependency repair is needed.

The stated proof-dependency modules are imported without `public`: ClosedPointField,
IsRegularIffDimensionDrop, WeilConjectures.AlgebraicGeometry.Regular,
WeilConjectures.RingTheory.ClosedPointDimensionLocalRing,
WeilConjectures.Topology.PresheafModuleStalkFunctor, Mathlib's Pullbacks,
Localization.AtPrime.Basic, Ideal.KrullsHeightTheorem, and Unramified.LocalRing.
The declaration signatures and docstrings of the recorded interfaces were read.
The existing Mathlib matches for affine fibre products, finite local dimension and
etale residue fields were read as their declarations, even though they have no lean record.
The unstated proof-only nodes lem-sfb-local-map-image-regular-sequence and
lem-trf-regular-local-regular-sequence-depth are named in the proof plan; they supply
no notion needed to type this statement and therefore no dependency module is added.

Edge cases checked before writing:

- d = 0: the empty list is allowed, Ideal.ofList [] is the zero ideal, and J cuts out
  the whole open. Regularity of the empty list is nontriviality of the stalk, which
  holds at an actual scheme point. The dimension assertion retains its full meaning.
- Empty schemes or spaces cannot supply u₀ and the rational point z. No independent
  nonemptiness hypothesis is imposed, and no case with the stated data is lost.
- Arbitrary fields, including imperfect fields and all characteristics, are admitted.
- The atlas point need not be rational over k; equality of point classes allows the
  finite separable extensions used by the proof.
- Nonreduced zero subschemes use the full generated ideal, not its radical.
- U and S may be non-Noetherian. The only local regularity comes from the smooth k-chart.
- Both dimensions are computed on the actual fibre products, at the specified point.

Searches for an existing statement:

- `msearch.py leanfinder`: “A smooth algebraic space over a field admits regular
  parameters from base functions when the fibre at a rational point has dimension
  zero” returned eight standard-smooth algebra and scheme chart results; no match.
- `msearch.py leansearch`: “Regular sequences of functions from a base scheme cut a
  smooth algebraic space over a field to dimension zero at a rational point” returned
  smoothness eliminators and regular-sequence recursors; no geometric assertion matched.
- `msearch.py loogle`: `"IsRegular", "Smooth"` returned zero hits.
- `msearch.py grep`: `smooth.*fibre.*parameter|image.*regular.*sequence` returned zero hits.
- `rg` in Mathlib, WeilConjectures and Sheaf for the proposed declaration and module
  found no match; `grep -rn` of the item id in WeilConjectures also found none.
  Concept searches in Sheaf found the existing point classes and etale dimension,
  which are reused rather than copied. The distinct local-dimension-chart-invariance
  theorem uses stalk dimension and is not used in place of etaleLocalDimension.

Source read: Stacks stacks-morphisms.tex Tag 06MF, the whole local-ring and final
local-dimension paragraph; algebra.tex Tag 06LC. The latest blueprint directory was
searched for the item: it is an auxiliary stage-1 node, not the unit's own statement.
There is no mathematical statement correction and no unresolved statement dispute.

Validation: scompile.py compiled the statement against the live published library with
no errors or warnings. The initial elaboration issue was resolved by spelling out
Over.homMk's source and target objects and qualifying Limits.pullback; the mathematical
statement did not change. Final preflight and per-file compile are recorded by deliver2.py.

## Second reading by Q61

Written by the maintainer's independent reviewer (the delivered section was the
dispatcher's "no second reading" placeholder). The node, Stacks stacks-morphisms.tex
Tag 06MF (paragraph "Consider the maps of étale local rings"), the Lean file and the
declarations of every statement dependency were open.

Objects and hypotheses of the node, with their Lean:

- S scheme: `{S : Scheme.{u}}`. Pass.
- k field over S: `(k : Type u) [Field k] (sk : Spec k ⟶ S)`. Pass; same universe as
  the schemes, as def-trf-algebraic-space fixes.
- U/S scheme, u closed: `(U : Over S) (u₀ : U.left) (hu₀ : IsClosed {u₀})`. Pass; no
  Noetherian, finite-type, affine or separatedness assumption.
- E/k algebraic space, smooth over k: `E : AlgebraicSpace S` with structure map
  `q : E ⟶ h_{Spec k}` and `hq`: every representable-étale scheme chart
  `a : h_T ⟶ E` has `T → Spec k` `Smooth`. Smoothness is étale local on the source,
  so this is the same as testing on one atlas; it is not stronger. Pass.
- p : E → U an S-morphism, not assumed k-linear: `p : E.obj.obj ⟶ yoneda.obj U`.
  Pass (06MF has the same situation: F → u smooth, p : F → U).
- z a k-rational point: `z : h_{Spec k} ⟶ E`, `hz : z ≫ q = 𝟙`. Pass.
- image u and κ(u) → k an isomorphism: `e : Over.mk sk ≅ Over.mk (Spec κ(u₀) → U → S)`
  and `he : z ≫ p = h(e.hom) ≫ h(residue point)`. A morphism Spec k → U with image u
  factors uniquely through Spec κ(u) → U; the factor is over S because z and p are,
  and it is an isomorphism exactly when κ(u) → k is one. Equivalent. Pass.
- dim_z(E ×_U Spec κ(u)) = 0: `etaleLocalDimension` (def-sfb-algebraic-space-etale-dimension,
  sup over representable-étale scheme charts of `topologicalKrullDimAt`, the infimum
  over open neighbourhoods) of the presheaf pullback of p and h(Spec κ(u) → U), at the
  point class (def-a1-algebraic-space-point-classes, `schemePointMap`) of
  `pullback.lift z (h e.hom) he`. This is the node's chart convention. Pass.

Conclusion clauses:

- affine open U' ∋ u: `∃ O, IsAffineOpen O ∧ u₀ ∈ O`. Pass.
- d ≥ 0 and f₁,…,f_d ∈ Γ(U',O): `fs : List Γ(O.toScheme, ⊤)`, d = length; empty
  list allowed. Pass.
- étale scheme chart V → p⁻¹(U'): `a : h_V ⟶ pullback p (h O.ι)`, `IsEtale a ∧
  IsSurjective a`. Pass.
- v ∈ V above z: equality of point classes in E of `a ≫ fst` at v and z at the closed
  point. A non-rational v is allowed, as the node's proof needs. Pass.
- pullbacks form an O_{V,v}-regular sequence: `RingTheory.Sequence.IsRegular` (the
  def-weil-pbc-regular-sequence declaration, including M ≠ (f)M) of the germs at v of
  `(a ≫ snd)`-pullbacks of the fᵢ. Pass.
- fᵢ vanish at u: `Γevaluation ⟨u₀, hu⟩ f = 0` for f ∈ fs. Pass.
- Z = V(f₁,…,f_d): `J = IdealSheafData.ofIdealTop (Ideal.ofList fs)` on the affine O,
  i.e. the quasi-coherent ideal generated by the fᵢ (not its radical); Z = J.subscheme.
  Pass.
- z ∈ E ×_U Z: `∃ zJ, zJ ≫ fst = z`. Since Z → U is a monomorphism the second
  component is forced, so the point class of zJ is determined. Pass.
- dim_z(E ×_U Z) = 0: `etaleLocalDimension … (schemePointMap zJ closedPoint) = 0`. Pass.

Quantifier order: ∃ U', fs, V, a, then ∃ v and the regularity, then Z and the
dimension; the same as the node.

Edge cases: d = 0 (empty list, J = 0, Z = U', regularity = stalk nonzero); empty S, U
or E cannot carry u₀ and z; any characteristic and imperfect k; non-Noetherian U.
All covered.

Records: the node differs from the live node only by `lean` and the two added
statement dependencies, which are landed definition nodes whose declarations
(`Point`/`schemePointMap`, `etaleLocalDimension`) the statement uses. `lean.statement`
is verbatim the signature in the file. No definition is introduced; the only proof is
`sorry`; module and declaration docstrings carry the source place and
`(blueprint: lem-sfb-smooth-fibre-image-parameters)`, and the declaration docstring has
the six proof steps. No pro-étale substitute is used.

Searches: Mathlib `IdealSheafData.ofIdealTop`, `Sequence.IsRegular`; the Sheaf tree
for existing point classes and étale dimension (reused, not copied). No existing
declaration states this lemma.

Mismatches found: none in the Lean. Changed: only this section.
