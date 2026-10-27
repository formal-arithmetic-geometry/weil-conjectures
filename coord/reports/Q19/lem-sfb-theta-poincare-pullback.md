## Worker report

Module: `Sheaf.AlgebraicGeometry.ThetaPoincarePullback`.
Main declaration: `AlgebraicGeometry.exists_theta_poincare_pullback_iso`.
Four auxiliary definitions give the actual negative-theta module, difference
module, its Abel-times-inversion pullback, and the zero axis. All have real
construction data; only the main theorem has `sorry`. No new nodes, dependency
repairs, statement correction, or disputed statement.

Source read: `literature/milne-abelian-varieties_AV.pdf`, PDF pp.111–113,
printed pp.105–107, especially III 6.8(b). The negative theta and second-factor
inversion agree with the source and the node. The six proof steps are retained
in the theorem docstring, including dense-open extension and both rigidifications.

Hypothesis and clause correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Smooth projective connected curve: explicit structure map `f`, with
  `[IsConnectedCurve f] [Smooth f] [IsHProjective f]`. The first includes
  nonemptiness, dimension one, finite type and separatedness. No extra properness
  or geometric-integrality hypothesis: the dependency's
  `pointedAbelGeometricIntegrality f` supplies the latter, and projectivity gives
  properness for the Jacobian interface.
- Genus g at least one: `(g : ℕ) (hg : f.genus = g) (hgpos : 1 ≤ g)`.
- Rational point P: `P : Spec (.of k) ⟶ C` and `hP : P ≫ f = 𝟙 _`.
- Fixed Jacobian with representing isomorphism: `J`, `[GrpObj J]`, `hJ`,
  `eJ : (picardFunctorDegree f 0).obj.RepresentableBy J`, and
  `heJ : IsPicardZeroMul f eJ`. This is precisely the dependency interface,
  including compatibility with the group law.
- Universal degree-zero family: `M : (pullback f J.hom).Pic` is the class of
  an actual invertible module; its representative is `(fromSkeleton _).obj M.val`.
  `hM` is fibrewise degree zero and `hMid` identifies its image with `eJ.homEquiv
  (𝟙 J)`. This specifies the identity family, not an arbitrary bundle.
  `hMnorm` and `hMzero` give the prescribed trivial class on P times J and
  C times zero. Actual axis identifications are retained below.
- fP(Q) = [O(Q-P)]: `N` and `hN` identify N with the ideal of P, O(-P).
  `hfP` specifies fP on EVERY test scheme T and every section Q by the dual
  graph ideal, O(graph Q), tensored with the pullback of N. Its image under
  sheafification is `eJ.homEquiv (Q ≫ fP)`. These are the recorded dependency's
  objects and signatures; the map is not specified just on rational points.
- Effective divisors of degree g-1: `H` with the representing equivalence `eH`
  of `hilbertPresheaf f (g - 1)`. The latter is the existing relative effective
  Cartier divisor functor. The condition `ha` specifies a on EVERY test scheme
  by O(D) tensor O(-(g-1)P), using the actual ideal of `eH.homEquiv v`.
  This is the degree-(g-1) construction of the symmetric-Abel dependency,
  with its degree-shift formula substituted into the Abel formula. It imposes
  no new geometric hypothesis. No assumptions of birationality, dimension,
  closed immersion or Cartierness have been added: those are consequences
  available from that dependency.
- Theta is the scheme-theoretic image: `a.left.ker` is its ideal sheaf, so
  `a.left.ker.toModulesᵛ` is O(Theta). It is not a set-theoretic image.
- Theta-minus and L: `negativeThetaModule a` is the recorded explicit
  `tensorPullback` along `ι[J].left` of that dual ideal module. Pullback along
  inversion agrees with the line of the inversion pullback divisor.
- L0: `thetaDifferenceModule a` is exactly the parenthesized tensor of
  addition pullback L, first projection pullback L-dual, and second projection
  pullback L-dual. `μ[J]`, `fst J J` and `snd J J` are the canonical morphisms
  of the group object and its product in `Over (Spec k)`.
- fP times inversion: `thetaAbelPullbackModule fP a` uses the actual tensor
  product map `(fP ⊗ₘ ι[J]).left`, and the recorded `tensorPullback` functor.
- Indicated normalizations: `sectionBaseChange f P hP J` is P times J;
  `thetaZeroAxis f J` is C times zero. `rP` and `r0` are the prescribed
  isomorphisms between the restrictions of the two bundles, obtained by
  composing their specified trivializations with inverses. This records the
  normalization without arbitrary choices of bases for the origin line.
  Conversely any such axis identification is obtainable from trivializations,
  since both restrictions are trivial by the stipulated normalizations.
- Compatibility at (P,0): `hcorner` compares the pullbacks of `rP` along
  `η[J].left` and of `r0` along P. The canonical
  `tensorPullbackSectionComp` isomorphisms identify iterated restrictions
  with the composite-map pullbacks. The two composites of scheme maps are equal
  (both (P,0)); `HEq` expresses equality of these morphisms across their equal
  dependent Hom types. It is equality with the canonical equality transport,
  not equality up to an arbitrary automorphism or just equality of classes.
- Conclusion: an actual module isomorphism `e` from the displayed pullback to
  the representative of M. The two equations on its pulled-back homomorphism
  require exact agreement with BOTH prescribed axis identifications.

Dependency declarations read and reused:

- Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`, and `IsAlgClosed`, in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`; the algebraic-closure node's match
  explicitly includes the latter, so no unnecessary closure choice is made.
- `WeilConjectures.AlgebraicGeometry.Curve`: `IsCurve`, `IsConnectedCurve`,
  `Scheme.Hom.genus`, with their full signatures and docstrings.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`: `IsJacobian`;
  `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`: degree functors and
  `IsPicardZeroMul`.
- `Sheaf.AlgebraicGeometry.SymmetricAbelImageGeometry`:
  `pointedAbelGeometricIntegrality`, `exists_pointedAbel_image_geometry`;
  its full universal family, graph, Hilbert and degree-shift signatures were read.
  Its public imports also expose the recorded divisor construction
  `Sheaf.AlgebraicGeometry.DivisorModule` and Hilbert/Picard interfaces.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible` (the locally-free-rank-one notion).
  The dependency Picard classes package exactly invertible modules, so their
  existing representative operation is reused instead of defining new classes.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  upstream `Scheme.Modules.tensorPullback` and canonical
  `tensorPullbackSectionComp`; every newly written module pullback uses them.
  Picard-group maps use the existing `Scheme.Pic.map` required by the
  recorded family and Abel-map interfaces, without redefining them.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `Scheme.IdealSheafData.toModules`, `Scheme.Modules.dual`,
  `Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules`.
  Its source docstring identifies the dual ideal with O(D).

Statement dependency modules are public imports, directly or through the
symmetric-Abel module's public imports. All currently recorded proof-only
modules are plain imports: ProjectiveSpace, SmoothComponentPureTranscendental,
AbelianVariety.Defs, Proper, Smooth, PicardFiberTrivialityClosed, DensePoints and
Geometrically.Integral. The generic-theta-Abel-Cartier-pullback and
rigidified-product-seesaw nodes currently have no recorded declaration, so have
no module to import; their proof steps remain explicit in the docstring.

Edge cases checked: g=1 uses H representing degree-zero divisors and N^0=1,
so Theta is the reduced origin and no positive-degree-only restriction occurs.
g=0 is explicitly excluded by the node. The point and connected-curve
hypotheses exclude the empty scheme. No characteristic restriction is imposed;
in characteristic two inversion remains the actual group inversion morphism.
All test schemes T have the existing framework's full scheme universe u.
Nonreduced/disconnected T are included. The intersection of the two axes is
not discarded: hcorner is necessary since incompatible independently rescaled
normalizations cannot extend to one isomorphism. Taking identity isomorphisms
when the bundles agree satisfies this corner condition.

Searches (msearch.py Q19 lem-sfb-theta-poincare-pullback):

- leanfinder: "The normalized Poincare line bundle on a curve times its Jacobian
  is the pullback of the theta difference line bundle along the Abel map times
  inversion"; 8 hits, including AffineSpace.isPullback_map, Proj pullback
  projection formulas, WeierstrassCurve.Affine.Point.toClass and scheme pullback
  coordinate identities. None states the node.
- loogle: `"Poincare"`; 0 hits.
- grep: `Poincare|Poincaré|theta.*divisor`, AlgebraicGeometry; 0 Mathlib hits.
- leansearch: "The normalized universal Picard bundle on a curve times its
  Jacobian is the pullback of the theta difference bundle along the Abel map
  and inversion"; 8 hits, all general bundle pullbacks, normalization morphisms,
  or Weierstrass polynomial formulas; no theta/Picard identity.
- rg in lean/WeilConjectures and lean/Sheaf for
  `Poincare|Poincaré|theta.*[Pp]ullback|thetaDifference`: general cohomological
  Poincare duality, unrelated comparison morphisms and the symmetric-Abel module;
  no existing statement of this identity or helper module.
- grep -rn for this node id in lean/WeilConjectures: no hits. rg of
  dag/lean_names_upstream.json for Poincare/thetaDifference/theta_poincare:
  no matching declaration of this node.

Validation: prescribed scompile.py, server confirmation, clean in 2.9 seconds.
The local overlay initially reported OSError(28) (no space); the unmodified
wrapper's automatic server fallback succeeded with exit 0. Earlier elaboration
errors were repaired: use Picard representatives for the existing class
interface, and tensorPullback consistently in the new constructions. No direct
build or git operation was run in the shared read-only repository.

## Second reading by Q19

I reopened the node and re-read the finished module clause by clause. This is
a separate self-check; the dispatch brief forbids starting another agent and
assigns the independent review to the maintainer. The full hypothesis/clause
matching is above. The check caught an initial use of Mathlib pullback in the
new module constructions and a mismatch between scheme and sheaf invertibility
instances; these were repaired using the recorded tensorPullback and the
existing Picard-class representative. Both signs, every tensor factor, the
scheme-theoretic image, all-T Abel characterizations, and BOTH final axis
equations were rechecked. No node statement change was needed.
