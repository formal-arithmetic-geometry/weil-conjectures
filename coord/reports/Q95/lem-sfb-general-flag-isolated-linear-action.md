## Worker report

Item: lem-sfb-general-flag-isolated-linear-action. The module
`Sheaf.AlgebraicGeometry.GroupScheme.GeneralFlagIsolatedLinearAction` states
`AlgebraicGeometry.exists_general_flag_isolated_linear_action`, with a sorry proof only.
The mathematical statement is unchanged. Its nine-step natural-language proof is in the
statement docstring. The source was read directly from the supplied Milne PDF: Theorem 4.27
and Remark 4.30, printed pp.94--96, Section 17f and Lemma 17.52/Proposition 17.53,
pp.368--369, Theorem 13.1, p.254, Lemma 13.51 and its following discussion, pp.274--275,
and the first paragraph of Theorem 17.65, p.374. This is the general connected group case.

Hypothesis and conclusion correspondence:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- F-group scheme G: `G : Over (Spec (.of F))` with `[GrpObj G]`.
  Smoothness, connectedness, affineness and finite type are respectively
  `[Smooth G.hom]`, `[ConnectedSpace G.left]`, `[IsAffine G.left]`, and
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`. No reductivity is assumed.
- B is a group scheme with embedding `iB : B ⟶ G` and
  `hB : IsBorelGroupScheme iB`. Its existing definition includes the closed-subgroup
  condition, smoothness, connectedness, scheme-theoretic derived-series solvability,
  and maximality among such closed subgroups. `IsDerivedGroupScheme` in its imported
  Semisimple module is the smallest closed subgroup through which the commutator factors.
- Q represents the fppf sheafification of right cosets: Q is an arbitrary F-scheme;
  `ηQ` has source the presheaf coequalizer of projection `(g,b) ↦ g` and right
  multiplication `(g,b) ↦ giB(b)`. Coequalizers of presheaves are pointwise, so this
  is exactly the coset presheaf, without a normality assumption on B. `hηQ` is its
  sheafification universal property: maps from Q to every fppf sheaf correspond bijectively
  to maps from the coset presheaf. Representables are fppf sheaves by subcanonicity.
  The big slice fppf site has the same restriction to affine test algebras as the
  statement, by affine refinement; there is no change of quotient.
- The canonical quotient map is `q`, normalized by `hηq` on the coequalizer generators.
  `[ModObj G Q]` is the given left scheme action and
  `hq : μ[G] ≫ q = (𝟙 G ⊗ₘ q) ≫ γ[G,Q]` says it is induced by left multiplication.
  These presentation binders express the quotient and action specified in the node;
  they impose no extra property. The theorem holds for every such presentation.
- Nonzero finite-dimensional E: choose `n : ℕ` and take
  `E = ULift (Fin (n+1)) → F`. It has its actual coordinate basis, finite dimension
  n+1, and is nonzero. Choosing a basis identifies every nonzero finite-dimensional
  vector space with such a model, so this is exactly the existential assertion.
- Rational representation: `ρ : G ⟶ GeneralLinearGroup (ULift (Fin (n+1))) F`,
  with `IsMonHom ρ`. Upstream GL is Spec F[x_ij,det^-1] with its Hopf group law;
  `GeneralLinearGroup.homMulEquiv` identifies its A-points with invertible matrices,
  equivalently A-linear automorphisms of the actual scalar extension of E.
- P(E) parametrizes lines: `linearProjectiveSpace F (ULift (Fin (n+1)))` is the
  existing total-degree polynomial Proj with its existing structural map. The bound
  action `a` has `IsStandardProjectiveLinearAction ... a`, which prescribes
  z_i ↦ sum_j x_ij z_j, the action on homogeneous column coordinates of lines.
  It does not use the dual/contragredient action.
- The embedding is the F-morphism `j` with `IsClosedImmersion j.left`.
  `γ[G,Q] ≫ j = (ρ ⊗ₘ j) ≫ a.smul` is equality of F-scheme morphisms;
  evaluating on any algebra gives exactly i(gx)=ρ(g)i(x), including nilpotents.
- The cocharacter is `cochar : StandardGroupSchemes.multiplicative F ⟶ G`
  with `IsMonHom cochar`. There is no nontriviality or injectivity condition.
- The fixed subscheme is H with closed immersion `jH : H ⟶ Q`.
  Its displayed equivalence says an A-point factors through H exactly when,
  for every algebra A', algebra morphism f:A→A', and A'-point t of Gm,
  `(t ≫ cochar) • x_A' = x_A'`. These are all algebra extensions, not just fields,
  and the Laurent Hopf Gm points are exactly A'^×. Closed immersion supplies uniqueness
  of the factorization, so this is representation of the stated fixed subfunctor.
- The final `∃ r : ℕ, Nonempty (H ≅ ∐ fun _ : Fin (r+1) ↦ 𝟙_ ...)`
  is an isomorphism over F to a positive finite disjoint union of Spec F. It asserts
  reducedness and the full scheme structure, rather than merely counting rational points.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field; Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed.
- Mathlib.CategoryTheory.Monoidal.Grp: GrpObj, IsMonHom; its internal monoid and inverse
  diagrams encode the group scheme. Mathlib.CategoryTheory.Monoidal.Cartesian.Mod:
  ModObj and the action on test-point hom sets.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: IsSubgroupScheme and
  IsClosedSubgroupScheme, including the actual homomorphism and closed immersion.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: Smooth;
  Mathlib.Topology.Connected.Basic: ConnectedSpace;
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact.
- Mathlib.AlgebraicGeometry.Sites.Fpqc: Scheme.fppfPrecoverage, Scheme.fppfTopology;
  Mathlib.CategoryTheory.Sites.Over: the slice topology;
  Mathlib.CategoryTheory.Sites.Sheafification: presheafToSheaf and its adjunction.
  The displayed universal property avoids an arbitrary sheafification choice.
- Mathlib.LinearAlgebra.FiniteDimensional.Defs: FiniteDimensional is Module.Finite;
  its finite coordinate-space instance renders the node's finite-dimensional existence.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion;
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective: IsHProjective/IsProjective;
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace: polynomial Proj and structural map.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: multiplicative and multiplicativeGroup,
  the actual Laurent Hopf group scheme; affine and map describe test algebras.
- Added already landed definition dependencies: def-sfb-borel-subgroup-scheme,
  `Sheaf.AlgebraicGeometry.GroupScheme.Borel`, `IsBorelGroupScheme`; and
  def-sc-general-linear-group, whose GL component is the canonical upstream
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`, `GeneralLinearGroup`,
  with `homMulEquiv` on all test algebras. No dependency interface was replaced.
- Each already recorded proof-dependency module is imported plainly, including
  GeneralBorelFlagVariety, SmoothGroupOrbitGeometry, HomogeneousOrbitQuotientGeometry,
  SmoothAlgebraReduced, BorelMaximalTorusConjugacy, GmRepresentationWeightBasis,
  TorusFixedSchemeSmooth, EnlargedEtaleRingedSite, Regular and IsRegularScheme.
  Mathlib proof leaves are imported through their defining modules or existing dependencies.
  The unstated proof-only prerequisites are named in the docstring, not restated.

Edge cases checked: G=B, the trivial group, solvable groups, and rank-zero tori all permit
Q=Spec F and a trivial cocharacter. n=0 means E=F and P(E)=P^0, so a point quotient
is included. The fixed scheme cannot be empty because the coproduct has r+1 components.
Characteristic is unrestricted. Both the zero test algebra and nonreduced test algebras
are included in CommAlgCat. All universes and variables are explicitly bound; algebra
objects have the field's universe, as in the existing group-scheme site convention.
The helper definition also permits an empty coordinate set (empty projective scheme).

Searches: msearch.py leanfinder for a connected affine group's Borel quotient with a
projective embedding and finite reduced fixed locus returned Proj, properness and unrelated
Galois/representation results, no exact theorem. msearch loogle for
`AlgebraicGeometry, Projectivization, GeneralLinearGroup` returned no matches/unknown
identifier; grep `Borel|cocharacter|Projectivization|GeneralLinear` in AlgebraicGeometry
returned none. The helper-specific LeanSearch and LeanFinder searches found only
field-valued Projectivization group actions and matrix definitions; loogle
`Proj.map, Matrix.GeneralLinearGroup` returned unknown identifier; grep
`GeneralLinear.*[Pp]roject|[Pp]roject.*[Aa]ction` returned an unrelated structure-sheaf
comment. Exact wrapper output is preserved in the new node's mathlib_searches.
Direct rg in WeilConjectures and Sheaf found the existing GL, Borel and diagonal-action
interfaces but neither this theorem nor a general GL action on polynomial Proj.
The requested node-id search in WeilConjectures found no occurrence. A final full-name
search in both project trees and Mathlib found no declaration collision.

Validation: scompile.py compiled each file separately, in dependency order, in both
sandbox and library positions against the published live build. No errors or non-sorry
warnings. The new definition has real data throughout and no postponed theorem.
The main theorem has one sorry. No statement dispute or source correction was needed.

## New nodes

def-sfb-standard-projective-linear-action owns
`Sheaf.AlgebraicGeometry.GroupScheme.StandardProjectiveLinearAction` and its three
real-data definitions: linearProjectiveSpace, projectiveLinearCoaction, and
IsStandardProjectiveLinearAction. This is the matrix substitution on the existing Proj,
with full ring maps, irrelevant-ideal conditions, and both projections of the unique
base-change comparison. Its source is Milne's representation on lines (Theorem 4.27,
Remark 4.30 and the use in Theorem 17.65). No canonical action is replaced by an arbitrary
map: the action must have exactly the stated substitution. No existence assertion is
hidden in the definition. Mathlib's field-only Projectivization and the already landed
torus-specific IsDiagonal do not supply this notion for GL on schemes. DAG text search
and `tools/blueprint_refs.py search 'linear projective action'` found no existing node;
the latter returned zero matches. `blueprint_refs.py ancestor` returned None, inherited
from the item's existing blueprint origin. The new node preserves that origin and
prepends this item to its via chain. The item cites this node and the two existing
notion nodes above; no existing dependency record or statement is changed.

The maintainer performs the independent reading; this dispatcher-started worker has
not represented its own report as an independent second reading.

## Second reading by Q95

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
