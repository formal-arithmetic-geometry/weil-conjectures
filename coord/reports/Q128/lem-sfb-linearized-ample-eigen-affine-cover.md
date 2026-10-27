## Worker report

The delivery states `AlgebraicGeometry.exists_linearized_ample_eigen_affine_neighbourhood`
in `Sheaf.AlgebraicGeometry.LinearizedAmpleEigenAffineCover`. Its only theorem has
proof `sorry`. Six canonical implementation helpers belong to this same notion and
are recorded in `lean.declarations`; none introduces a new mathematical assumption,
a new independent notion, or unspecified data. The item statement and all existing
DAG fields except `lean` are unchanged. There are no new nodes, dependency repairs,
statement corrections, or disputed claims.

Clause-by-clause correspondence:

- A Noetherian commutative ring is `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
  The base is literally `Spec (.of A)`, and the torus is the recorded
  `relativeSplitTorus (Spec (.of A)) 1`, not a field-only multiplicative group.
- The scheme over S with its actual S-action is the bundled object
  `X : CategoryTheory.Mod (Over (Spec (.of A))) (relativeSplitTorus ... 1).X`.
  Its underlying scheme is `X.X.left`, structure map `X.X.hom`, and action map
  `ModObj.smul`. Mathlib's `ModObj.one_smul` and `ModObj.mul_smul` are exactly
  the unit and associativity identities as morphisms in `Over S`, hence as
  scheme maps. Cartesian tensor in `Over S` is the chosen scheme pullback.
- Separated and finite type are `[IsSeparated X.X.hom]`,
  `[LocallyOfFiniteType X.X.hom]`, and `[QuasiCompact X.X.hom]`.
- Normal local domains are `hnormal : ∀ p, IsDomain (X.X.left.presheaf.stalk p) ∧
  IsIntegrallyClosed (X.X.left.presheaf.stalk p)`; no condition on the base ring's
  normality, reducedness, or being a domain is added.
- The supplied line is `(L : X.X.left.Modules) [L.IsInvertible]`; its absolute
  ampleness is the recorded `Scheme.Modules.IsAmple X.X.left L`.
- The supplied forward isomorphism is `theta : p₂^* L ≅ a^* L` using the
  recorded `Scheme.Modules.tensorPullback`, not a fresh pullback functor.
  `relativeLineLift` pulls it back along `(g,x)` using the uniquely normalized
  composition comparisons. `hunit` is its identity law and `hmul` is its
  multiplication law on every test scheme. These are equalities of sheaf
  isomorphisms, not equalities of residue-field values. `HEq` only handles the
  propositionally equal source/target pullbacks under the action identities;
  it does not forget any compatibility. Naturality follows from the actual
  pullback of the single global `theta`, so no extra naturality input is needed.
  Conversely, the universal test schemes X and T×T×X recover precisely the
  identity and cocycle sheaf-map equations in the node.
- For each `(x : X.X.left)`, the existential binds `n : ℕ`, `0 < n`, `w : ℤ`,
  and `s : Γ(L.tensorPow n, ⊤)`. Thus the exponent is positive and the character
  weight may be negative, zero, or positive, exactly as in the node.
- `U : X.X.left.Opens`, `x ∈ U`, `IsAffineOpen U`, and
  `(U : Set X.X.left) = Scheme.Modules.nonvanishingLocus (L.tensorPow n) s`
  give exactly x∈X_s and affineness of that very nonvanishing open.
- `a ⁻¹ᵁ U = p₂ ⁻¹ᵁ U` is scheme-theoretic invariance: the action factors through
  U on T×U, and the inverse action proves the reverse inclusion. Open subschemes
  are determined by their opens, so this neither adds nor drops structure.
- `relativeLinePowerLift` is the induced tensor-power action. It uses the existing
  `PGLLinearization.powerIso` (whose signature is over arbitrary schemes and has
  no field argument), the recorded tensor-pullback tensor comparison normalized
  on pure tensor sections, and the structure-sheaf comparison at n=0.
  `relativeLinePullbackSection` is the actual section pullback via the normalized
  adjunction unit. No arbitrary isomorphism, scalar action, section map, or
  trivialization is chosen.
- `relativeTorusWeight S Q g w` pulls the actual Laurent basis element e_w along
  the projection in the definition of `relativeSplitTorus` and the test map g.
  The `ΓSpecIso` inverse turns the coordinate element into a global section.
  Hence for g=t on Spec B this is t^w; on X_B it is that unit pulled back.
  It does not assume a chosen identification of global sections after base change.
- The final equality is
  `theta^n_(g,y)(s(y)) = g^w • s(gy)` as sections on every test scheme Q over S.
  Taking Q=X_B, y the projection, and g=t pulled back from Spec B gives the
  desired equality on X_B. Replacing y by g⁻¹y gives literally the node's formula
  `(g·s_B)(y)=theta^n_(g,g⁻¹y)(s_B(g⁻¹y))=g^w s_B(y)`.
  Conversely, the node's all-algebras equality implies the stated all-test-schemes
  equality by restriction to affine opens of Q and pullback. Thus this formulation
  is equivalent, not an additional conclusion. Every commutative A-algebra in
  the scheme universe is allowed, with no nonreduced or nonflat case removed.
- The theorem asserts existence for each point only. It does not assert an
  invariant affine basis for arbitrary opens or any global-section base-change
  isomorphism.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.RelativeSplitTorus`: `relativeSplitTorus`, read in full;
  its base-change Hopf construction is also used to evaluate the canonical weight.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  alongside `IsDomain`, applied inline to the actual local rings.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; Cartesian tensor in `Over S` uses these.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `tensorPow`.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`,
  `Scheme.Modules.nonvanishingLocus`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionAdjunction`,
  `tensorPullbackSectionComp`; its full normalization and signatures were read.
- Additional existing canonical implementation APIs:
  `PGLLinearization.powerIso` from `PGLLinearizedPolarization`,
  `Scheme.Modules.module_pullback_tensor` from `ModulePullbackTensor`, and
  `tensorPullbackObjUnitToUnit` / `tensorPullbackObjUnitToUnit_isIso` from
  `TensorPullbackStructureSheaf`. The tensor comparison's pure-tensor
  normalization determines its map uniquely; its use of `Classical.choose` is
  on that canonical universal-property comparison, not unconstrained existence.

The recorded proof modules are imported privately: Noetherian schemes, relative
split-torus invariant affines, reduced induced closed subschemes, ample ideal
sections, and affine intersections with section opens. The proof-only node
`lem-sfb-relative-linearized-line-sections-coaction` has no recorded declaration
at reading time, so there is no module to import; the theorem's signature does
not require a coaction object or that theorem as an input.

Sources read: `literature/stacks-project/properties.tex`, the full statement and
ideal-section argument of `proposition-characterize-ample` (01Q3), and
`lemma-affine-cap-s-open` (01PV); the latest blueprint's
`sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3). The item is the
accepted auxiliary refinement rather than a verbatim Stacks theorem.

Edge cases checked: empty X makes the pointwise assertion vacuous; A=0 forces
empty S and X and is allowed; nonreduced and disconnected base rings are allowed;
normality concerns X only; no connectedness, properness, or field hypothesis is
introduced. The rank is exactly one as required. n=0 is excluded by `0 < n`, but
its canonical tensor construction is still defined. Negative weights use the
actual group-algebra basis and thus inverse powers. For a trivial X-action and
line character k, the forward equation forces the expected weight w=k. Arbitrary
nonflat B requires only pulling back a section; nowhere is Γ(X,L)⊗B identified
with Γ(X_B,L_B). The zero section cannot witness membership in U at the given x.

Searches made (all negative for an exact statement):

- msearch LeanFinder: “An ample linearized line bundle for a multiplicative group
  action has affine nonvanishing charts from eigensections of positive tensor
  powers”: 8 hits, Proj affine covers, basic-open localization and an unrelated
  convex `AmpleSet.image`; none gives this statement or linearized line data.
- msearch Loogle: `AlgebraicGeometry.Scheme, "lineariz"`: 0 hits.
- msearch grep: `[Ll]ineariz|[Ee]igensection` in `AlgebraicGeometry`: 0 hits.
- msearch LeanSearch: “An ample linearized line bundle for a multiplicative group
  action has an affine open cover by eigensections”: 8 hits, ordinary Proj/scheme
  affine covers and free representation linearization; no match.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for linearization and eigensections,
  and the exact item id in `lean/WeilConjectures`: no existing statement.
  `GroupSchemeLinearization.Linearization` is field-only; the existing relative
  invariant-affines theorem does not give sections of the fixed supplied line.
  The existing power isomorphism is general and is reused. Searches for all seven
  introduced full declaration names in Mathlib/project sources found no clashes.
- DAG searches for linearization and relative coaction nodes found the field-only
  group-scheme linearization and the already-known proof-only coaction node;
  no new independent definition is required by the inline supplied theta laws.

Validation: scompile.py compiled the sandbox and module path cleanly within the
standard 60-second limit. Only the prescribed wrapper was used for compilation.

## Second reading by Q128

This is the author's separate second reading, not a claim of independent review;
the maintainer supplies the independent delivery review. I reopened the item and
read the complete Lean signature and each helper. Each ring, scheme, morphism,
local-normality, line, ampleness, forward-linearization and cocycle hypothesis
matches the corresponding node clause as detailed above. I checked especially
that the character sign agrees with theta going from p₂-pullback to a-pullback,
that `relativeTorusWeight` uses the correct projection of the actual base-changed
Hopf spectrum, and that the final identity is a sheaf-section equality over X_B,
not merely an identity on geometric points. I also checked that invariance concerns
the same U identified with X_s, and that no base-change isomorphism was slipped in.
During implementation I replaced use of Mathlib module pullback by the recorded
explicit tensor pullback throughout; all comparison and section helpers now use
its normalized adjunction. The field-only linearization was not specialized to
this base ring or copied. No remaining mismatch with the accepted statement was
found. No existing statement, proof, dependency list, or source was changed.
