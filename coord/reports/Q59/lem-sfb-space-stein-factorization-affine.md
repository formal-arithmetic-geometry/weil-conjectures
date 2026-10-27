## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceSteinFactorizationAffine` states
`AlgebraicGeometry.AlgebraicSpace.steinFactorization_affine`, with one postponed proof.
Its four helpers are real data: the pointwise commutative ring instance on the existing
compatible-section subring, an abbreviation bundling that ring, its chart evaluation
ring homomorphisms, and the spectrum of the existing scalar pullback homomorphism.
No object is chosen from an uncharacterized existence statement.

Hypothesis and clause correspondence:

- A commutative ring A: `(A : Type u) [CommRing A]`; no nonzero assumption.
- X an algebraic space: `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`.
  Spec of the universe lift of Z is the terminal scheme in this scheme universe;
  this is the existing absolute-space convention, not a hypothesis on X.
- T = Spec A and f: `f : X ⟶ schemeSpace (Over.mk
  (specULiftZIsTerminal.from (Spec (.of A))))`.
- Properness: `hf : MapIsProper f`, using the node's exact chart/topology predicate.
- B = Γ(X_et,O_X): `X.steinGlobalFunctions` is
  `RingCat.sectionsSubring X.smallStructureRings.obj`, bundled as a commutative ring.
  The existing `SmallEtaleModel` is a skeleton of affine etale charts and an etale
  basis; compatible sections on this basis are precisely sections on the full small
  etale site. This retains actual functions and their restrictions, not an arbitrary ring.
- A → B: the existing `affineGlobalScalar A ... (Iso.refl _) X f`.
- Z = Spec B: the explicit target of the existential q.
- Evaluation of functions: the first conjunct, for every `T : X.SmallEtaleModel`,
  says that the restriction of q to T is `T.toSpecΓ ≫ Spec.map
  (steinChartRestriction X T)`. `steinChartRestriction` sends b to its T component.
  A morphism of sheaves is determined on these covering charts, so this describes
  precisely the canonical evaluation morphism, and does not assert a stronger property.
- π induced by A → B: `steinAffineProjection A X f` is literally `Spec.map`
  of the preceding `affineGlobalScalar`.
- f = πq: the second conjunct gives the equality of underlying presheaf maps
  `q.hom.hom ≫ yoneda.map (Over.homMk ...) = f.hom.hom`; both category inclusions
  are faithful, so this is exactly equality of the algebraic-space morphisms.
- π integral: `IsIntegralHom (steinAffineProjection A X f)`. The recorded scheme
  integrality predicate is used. For this spectrum map it is equivalent to every b
  satisfying a monic polynomial over A, and imposes no finiteness condition.
- q proper: `MapIsProper q` with exactly the same definition as the hypothesis.
- Every K and Spec K → Z: `(K : Type u) [Field K]
  (z : Spec (.of K) ⟶ Spec X.steinGlobalFunctions)`.
- Every field extension L/K: `(L : Type u) [Field L] [Algebra K L]`.
- Nonempty and geometrically connected fibre: `ConnectedSpace (Point (...))`, where
  `...` is the sheaf pullback of q along the Yoneda map of `Spec L → Spec K → Z`.
  By fibre-product associativity this is `(X ×_Z Spec K) ×_K Spec L`.
  Mathlib's `ConnectedSpace` extends `PreconnectedSpace` and `Nonempty`; thus no
  nonemptiness clause is lost. For L = K with its identity algebra this also
  includes the original fibre. `Point` and its instance are the recorded atlas topology.
- No extra Noetherian, flat, finitely presented, reduced, or scheme-source assumption
  appears. All fields and schemes are in the same fixed universe, as in the recorded
  field-point convention; there is no unrelated smaller test-field universe.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, and `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its `EtaleSite`, `etaleForget`, and its actual regular-functions structure sheaf.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`
  (separated, finite type, universally closed), rather than the scheme-only predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.Integral`: `IsFinite` and
  `IsIntegralHom`; the latter renders the integral clause.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, establishing that the chosen sheaf fibre product
  in the displayed expression is the algebraic-space fibre product.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`;
  its underlying `Point` and field representatives were also read in PointClasses.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, the recorded field-extension encoding.
- Added existing definition owner `def-trf-scheme-algebraic-space`:
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, `schemeSpace`.
- Added existing definition owner `def-sfb-space-small-ringed-model`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`, `SmallEtaleModel`,
  `smallEtaleInclusion`, `smallStructureSheaf`, `smallStructureRings`.
- Added existing definition owner `def-sfb-space-affine-global-sections`:
  `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`, `affineGlobalScalar`, whose
  chart scalar formula and naturality were read. No second scalar pullback is defined.

The three added definition owners are already landed. Their full DAG closures were
checked and do not reach this item (133, 133, and 414 nodes respectively). No new
node or dependency module is necessary. No statement correction is made.

The proof docstring follows every one of the node's eleven proof steps, including
proper cancellation, Noetherian approximation, coherent Ext in degree zero, monic
relations descending along limits, flat strict henselization, idempotents, proper
closed-image nonemptiness, henselian clopen lifting and common field extensions.
All recorded proof-dependency modules with Lean records are imported privately,
and Mathlib proof leaves have their owning modules privately imported. Unstated
proof dependencies remain the existing DAG obligations; none is needed to type
the statement and none is replaced by an assumption.

Edge cases checked: A = 0 forces X empty; X empty over any A gives B = 0, Spec B
empty and no K-valued z, so the fibre conclusion is vacuous. No nonzero assumption
was added to A or B. Non-Noetherian or nonreduced A and X are retained. Disconnected
X is allowed: the ring B and its spectrum separate components, so connectedness
is asserted only for fibres of q. Arbitrary transcendental L/K and the identity
extension occur in the binders. No finite-presentation or flatness hypothesis was
inherited accidentally from the curve-family API.

Sources read: local Stacks `spaces-more-morphisms.tex`, full statements and proof
of lemma-stein-universally-closed (0A19), and theorem-stein-factorization-general
(0A1C); current `literature/blueprint/latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`,
clause (3). This is an auxiliary Stein input; the blueprint unit is unchanged.
There is no STATEMENT-DISPUTED finding. The former stage-1 blockage is explicitly
resolved by the current stage-2 standing brief, section 0.

Searches made through msearch.py:

- LeanFinder: “Stein factorization of a proper algebraic space over an affine scheme
  has integral global functions and geometrically connected fibres”: 8 scheme-only
  hits, including isIntegral_appTop_of_universallyClosed and IsIntegralHom; no match.
- Loogle: `AlgebraicGeometry.IsIntegralHom, AlgebraicGeometry.IsProper`: 0 hits.
- Mathlib grep: `stein|Stein|steinFactorization`, AlgebraicGeometry: 0 hits.
- LeanSearch: “Proper algebraic spaces Stein factorization integral global functions
  connected geometric fibres”: 8 scheme-only hits; no match.
- Local rg over WeilConjectures and Sheaf for Stein/steinFactor: the upstream
  `Scheme.Hom.steinFactorization_affine` is scheme-only and cannot state this item.
  No algebraic-space Stein statement exists. Search for this item id in
  WeilConjectures returned no hits. Search for global-functions and scalar-section
  constructions located `affineGlobalScalar` and its small-model dependencies;
  those existing declarations are reused.

Compilation: prescribed scompile.py compiled both sandbox and library module names
cleanly (2.7 and 2.6 seconds) after making the compatible-section commutativity
instance explicit and annotating the Over objects. Final imports are rechecked by
scompile/deliver2 preflight. Every universe and variable is bound explicitly,
`autoImplicit` is false, maximum line width is 91, and the only theorem proof is sorry.

## Second reading by Q59

The dispatcher explicitly forbids other agents, so this is a separate self-audit,
not a claim of an independent worker review; maintainer independent review remains
required. Reopened the node and delivered file and traced the clauses above.
The initial construction needed an explicit pointwise CommRing instance because
smallStructureRings is valued in RingCat; the added instance uses the original
commutative chart rings and Subring.toCommRing, with no postponed data. The initially
ambiguous Over.homMk arguments were fixed by spelling out source and target.
The final q restriction equation fixes evaluation on all affine charts. Its target
is exactly Spec of the compatible-section ring; π is exactly the spectrum of the
existing scalar map. Factorization has the correct contravariant orientation.
IsIntegralHom is about π, MapIsProper is about q, and hf is about f. ConnectedSpace
includes the demanded nonemptiness, for all K, z, L and Algebra K L. The identity
extension is present and the zero-ring/empty-space case is not ruled out. The use
of Spec ULift Z only gives the canonical ambient absolute category. No discrepancy
with the unchanged node statement was found. The three additional stmt_deps name
existing construction owners, not newly assumed theorems or changes to the split.
