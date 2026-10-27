## Worker report

The delivery states `AlgebraicGeometry.RelativeRootExponential.exists_unique` in
`Sheaf.AlgebraicGeometry.GroupScheme.RelativeCanonicalRootExponential`. Its only
postponed proof is that theorem. Every helper is a concrete construction or a
predicate spelling out clauses of this node; none chooses a basis or a map from
an unconstrained existence statement. The node's natural-language statement,
proof, and dependency fields are unchanged. No new or dependency nodes are needed.

Source read: Conrad, *Reductive group schemes*, Theorem 4.1.4, printed p.110,
proof pp.116–118, Definition 4.2.3 and Remark 4.2.4, printed p.119, at
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf . The preceding paragraph
on p.110 explicitly constructs W(E)=Spec Sym(E*) and identifies its Lie algebra
with E compatibly with base change. The theorem supplies uniqueness, closedness,
and base change; its proof identifies the image as the smooth attracting root
group. The statement here retains the node's Noetherian affine-base specialization.

Hypotheses and objects, clause by clause:

- A is `Type u` with `[CommRing A] [Nontrivial A] [IsNoetherianRing A]`;
  the base is everywhere the existing `Spec (.of A)`.
- r is the explicit implicit binder `{r : ℕ}`. The torus is the existing
  `ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))`, constructed from the group
  algebra Hopf structure. ULift is an equivalence of the actual character lattice
  Z^r with a type in the ring universe; it imposes no restriction on characters.
- G is the existing `Grp (Over (Spec (.of A)))`. This is the group-object data,
  including all diagrams, from `def-sc-group-scheme`, valid over this base too.
- Smooth affine finite type means `[Smooth G.X.hom] [IsAffine G.X.left]`
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`. No separatedness,
  flatness, local-ring, characteristic, global splitting of the root line, or
  additional finite-presentation hypothesis was introduced.
- The closed torus inclusion is `i` with `[IsClosedImmersion i.hom.hom.left]`.
- `hred` uses the existing field-level `ReductiveTorusCentralizer.IsReductive`
  on every algebraically closed A-field pullback. Its definition uses the
  recorded geometric matrix-unipotence predicate; the latter includes smoothness
  and a faithful closed embedding into a general linear group. Thus the excluded
  subgroups are exactly smooth connected normal unipotent closed subgroups.
- `hmax` applies `ReductiveTorusCentralizer.IsMaximalTorus` to the same pullback
  of i on every algebraically closed A-field. This is maximality under inclusion
  among tori, using the recorded split-after-algebraic-closure notion.
- The auxiliary existing `ModObj` parameter a is tied to the actual conjugation
  morphism by `hconj`: its map is `(fst ≫ i) * snd * (fst ≫ i)⁻¹`. These are not
  arbitrary weight data. Conjugation supplies this action for every given i.
- `D : RelativeTangentWeights.Data r G a` uses the exact recorded dependency.
  `D.E`, its operations, normalization, naturality and differentiated equation
  identify `GrpObj.Lie G.X` with the specified dual-number kernel and identify its
  coaction with the actual differentiated action. The dependency `exists_data`
  applies under precisely these smooth affine finite-type hypotheses because
  conjugation preserves multiplication. Hence parameterizing by this data adds
  no mathematical hypothesis. Its normalization and evaluation on the generic
  Laurent point fix the comparison and coaction, rather than allowing an arbitrary
  choice of tangent module or action.
- `α : ULift.{u} (Fin r → ℤ)` and `hα : α ≠ 0` are the nonzero character.
  `Line D α` is literally `SplitTorus.weightSpace D.rho α`, the kernel of
  `rho - (v ↦ v tensor e_alpha)`; it uses the full character coaction.
- `hrank : ∀ p : PrimeSpectrum A, Module.rankAtStalk (Line D α) p = 1` is local
  rank one. The already required D has `weight_projective α`, proving this module
  finite projective. For finite projective modules, rank one at every prime is
  exactly locally free of rank one. Thus no global freeness assumption is hidden.
- `vector D α` is exactly `Spec (SymmetricAlgebra A (Module.Dual A (Line D α)))`
  with its canonical structure map. `vectorPoint` evaluates each dual linear form
  on a tensor vector by `Module.Dual.baseChange`, then applies the existing
  symmetric-algebra lift and Spec. Finite projectivity makes these the canonical
  bijections B tensor L ≃ V(B), including nonflat and zero B.

Conclusions, clause by clause:

- q is an actual morphism `vector D α ⟶ G.X`, hence over Spec A.
- `IsExponentialOver D α i A` for its actual identity-base pullback expresses the
  group homomorphism, T-equivariance, and canonical tangent inclusion. Its first
  clauses preserve zero and addition on every test algebra C; this is precisely
  the additive vector-group law. These point equations are equivalent to the
  scheme group diagrams by affine Yoneda.
- `characterValue α t` is the Laurent monomial e_alpha evaluated using
  `Spec.preimage t.left`. The equivariance equation is therefore scalar
  multiplication by chi_alpha(t) against conjugation by i(t), for every C and
  every C-valued torus point, not only for residue-field points.
- `infinitesimal D α v` is the tensor map on coefficients `c ↦ epsilon*c` into
  `DualNumber C`. The last clause of `IsExponentialOver` equates q on this actual
  tangent point with `(D.E C ((Line D α).subtype.baseChange C v)).val`. This is
  the canonical tangent inclusion on the entire scalar-extended root line.
- The next forall q' clause proves uniqueness among all such homomorphisms;
  q' is not required to be an immersion or to satisfy any conclusion first.
- `IsClosedImmersion q.left` gives closedness. Thus q identifies its source with
  its closed scheme image, and `Smooth (vector D α).hom` and
  `GeometricallyConnected (vector D α).hom` say exactly that this image is smooth
  with geometrically connected fibres.
- `IsGeometricRootImage` gives, over every algebraically closed A-field Ω, a
  smooth connected closed group inclusion j, an actual isomorphism e from the
  source pullback to that group, and `e.hom ≫ j.hom.hom = pullback.map q`.
  The further all-test-scheme conjugation condition says it is T-normalized.
  Its tangent point range is exactly `D.E Ω` of Ω tensor the root line. By
  D's weight-base-change equation this is the alpha weight space of the geometric
  Lie algebra. These are precisely the characterization hypotheses of the
  recorded root-subgroup-parametrizations theorem; their uniqueness identifies
  this image with its alpha-root subgroup. e is automatically a group isomorphism
  since q preserves addition and j is a closed group inclusion.
- For every commutative A-algebra B, the statement names the actual
  `(Over.pullback (Spec.map ...)).map q`, proves `IsExponentialOver` for it,
  and proves equality to that map for every competing B-morphism with the same
  conditions. No Noetherianity or nonzeroness of B is required. `basePoint` is the
  canonical pullback lift and `forgetPoint` the canonical first projection, so
  these are the actual pullback maps, not arbitrary maps with an existence claim.
- This arbitrary-base uniqueness includes successive base changes A→B→C: the
  iterated pullback has the same character and tangent inclusion over C, and hence
  equals the direct pullback under the canonical pullback-composition isomorphisms.
  The final forall f clause also states the explicit natural tensor-point formula
  for every A-algebra homomorphism f:B→C. Composing it for f and g gives the same
  formula for g.comp f; closed images then commute with those pullbacks because
  q is a closed immersion. Nothing is selected anew after base change.
- No basis of the line occurs in any binder or construction.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`,
  `isNoetherianRing_iff_ideal_fg` (finite generation of every ideal).
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map` (full signatures read).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, and group-point laws;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` was read for the recorded
  group-scheme, subgroup and closed subgroup interpretation.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Sheaf.AlgebraicGeometry.RelativeTangentWeightBaseChange`: full `Data`,
  `exists_data`, `Kernel`, `dualMap`, `act`, and `evaluatedAction` read.
  `GrpObj.tangentPoint` from the recorded upstream Lie/Ring module is used in the
  geometric image predicate. `SplitTorus.weightSpace` and `baseChangeCoaction`
  from `Sheaf.RepresentationTheory.RelativeTorusBundleWeights` were read.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations`:
  full `TorusCharacterTangent.reductive_root_subgroup_parametrizations` signature
  and proof docstring read. Its existing reductivity and maximal-torus predicates
  are used verbatim through the imported terminology module. The tangent-range
  characterization identifies the geometric image with its unique root group.
- Proof-only imports include the recorded
  `contracted_smooth_curve_etale_linearization`,
  `Scheme.fpqcCover_of_smallEtaleCover`, and Mathlib's fpqc subcanonical topology
  and base-change-stable precoverage. The centralizer and relative dynamic
  attracting subgroup proof nodes have no recorded Lean modules, so none can be
  imported for those two proof steps. Their full DAG statements are retained in
  the proof docstring and the node proof dependencies, unchanged.

Edge cases checked: r=0 makes hα impossible, so the assertion is correctly vacuous;
rootless groups likewise cannot meet the rank-one condition. Disconnected bases
and nontrivial invertible root modules remain allowed by stalk rank and Spec Sym.
Neither alpha's divisibility nor residue characteristic is restricted: full
Laurent weights, not character differentials, are used. In positive characteristic
extra Frobenius additive maps fail the required full-torus character equation.
Nonreduced A, nonflat/non-Noetherian B, the identity base map, successive algebra
maps, and B=0 are included. Over B=0 all pullbacks are empty schemes, with their
unique arrows; no geometric point or nonzero test algebra is required.

Searches actually run for this item (msearch.py, group Q23 and this item):

- leanfinder: `A root line in a reductive group scheme over a ring has a unique torus
  equivariant additive exponential closed immersion`: 8 abstract root-pairing and
  Lie-root-system hits, no relative scheme root exponential.
- loogle: `"GroupScheme", "root"`: 0 hits.
- grep Mathlib/AlgebraicGeometry: `root.*[Ee]xponential|[Rr]oot[Ss]ubgroup|[Rr]eductive`:
  0 hits.
- leansearch: `A root line of a reductive group scheme has a canonical exponential
  compatible with arbitrary base change`: 8 hits (root-pairing scalar changes,
  nilpotent Lie derivation exponentials, real exponential); none states this node.
- rg in project `lean/WeilConjectures` and `lean/Sheaf` for the exact item id and
  root-exponential patterns: no existing statement. Chevalley matrix exponential
  modules concern a specified integral representation or field realization and
  do not give this basis-free relative line map or arbitrary-base uniqueness.
- rg for vectorGroup/VectorGroup/SymmetricAlgebra in the project and Mathlib found
  general symmetric-algebra/sheaf-vector-bundle constructions, but no recorded
  affine root-line point construction or canonical relative exponential. The
  specialized vector/point helpers here use Mathlib's existing SymmetricAlgebra,
  not a replacement algebra or a second definition of a recorded vector group.
- `dag/lean_names_upstream.json` was searched for root/exponential/canonical names;
  no exact relative root-exponential declaration attaches.

Validation: scompile.py compiled the module in sandbox mode (24.4s) and library
mode (18.3s), with no errors or warnings. All declarations use explicitly bound
variables and universes; both autoImplicit and relaxedAutoImplicit are disabled.
The report's independent mathematical review is supplied by the maintainer under
the direct-worker delivery rule. No STATEMENT-DISPUTED issue was found.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
