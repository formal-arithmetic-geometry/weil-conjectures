## Worker report

The module `Sheaf.AlgebraicGeometry.SymmetricAbelImageGeometry` states
`AlgebraicGeometry.exists_pointedAbel_image_geometry`, with its entire proof `sorry`.
It also exposes `pointedAbelGeometricIntegrality`, a fully written application of the
existing `GeometricallyIntegral.of_isSepClosed` theorem to the connectedness supplied
by `IsConnectedCurve.connectedSpace'`. This is an instance-construction helper for the
existing `IsJacobian` signature, not a new notion or a postponed mathematical lemma.
No item field except `lean` is changed; there are no new nodes or dependency modules.

The source read is Milne, Abelian Varieties, Chapter III, printed pp.88–89 and 91
(normalized families and rigidified pairs), pp.91–93 (pointed Abel embedding),
pp.100–103 (symmetric Abel images), and p.105 before Theorem 6.6 (theta divisor).
The degree-zero Hilbert endpoint and the scheme-theoretic image refinements are those
in the node's accepted proof, not additional geometric assertions.

Hypotheses, one by one:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Curve C over k: `C : Scheme.{u}` and `f : C ⟶ Spec (.of k)`.
- Connected curve of dimension one, separated and finite type:
  `[IsConnectedCurve f]`, using precisely the recorded curve definition.
- Smoothness: `[Smooth f]`; projectivity: `[IsHProjective f]`, the recorded finite
  projective-space embedding convention. No extra integrality, Noetherianity,
  geometric-integrality or relative-dimension hypothesis is imposed.
- Genus g at least one: `g : ℕ`, `hg : f.genus = g`, `hgpos : 1 ≤ g`.
  `f.genus` is the recorded genus, equal to dim H1 in this setting.
- Chosen rational point: `P : Spec (.of k) ⟶ C`, `hP : P ≫ f = 𝟙 _`.
- Fixed Jacobian: `J : Over (Spec (.of k))`, `[GrpObj J]`, and `hJ : IsJacobian f J`
  with its geometric-integrality argument explicitly constructed by the helper.
  This retains the existing abelian-variety and dimension requirements.
- Fixed representing group isomorphism: `eJ : (picardFunctorDegree f 0).obj.RepresentableBy J`
  and `heJ : IsPicardZeroMul f eJ`. These are the same representation and group-law
  compatibility as `IsJacobian.represents`, with the representing data fixed rather
  than replaced by a choice or by another representation.

Conclusions, one by one:

- Universal invertible sheaf on C times J: `M : (pullback f J.hom).Pic`.
  The actual sheaf is `(fromSkeleton _).obj M.val`; its invertibility is built into
  `Scheme.Pic` through the recorded `Scheme.Modules.IsInvertible`. Thus this existential
  class supplies an actual invertible module, without a hollow definition.
- Fibrewise degree zero: `hM : M ∈ (picardSubfunctorDegree f 0).obj (op J)`.
- Trivial on P times J: membership of `M` in `picardFunctorNormalized f P hP`.
  Its actual definition is `Pic.map (sectionBaseChange f P hP J) M = Pic.mk O_J`.
- Represents the identity: `eJ.homEquiv (𝟙 J) = toSheafify.app (op J) ⟨M,hM⟩`.
- Trivial on C times origin: `Scheme.Pic.map (baseChangeMap f η[J]) M = 1`.
  The unit of Pic is the structure module; eta is the group-scheme origin.
- Pullback classification on every k-scheme T: for every normalized degree-zero
  `L : (pullback f T.hom).Pic`, there is a unique `a : T ⟶ J` with
  `Pic.map (baseChangeMap f a) M = L`. This is the canonical Picard pullback,
  not an arbitrary map into the Picard group.
  Normalized underlying classes are exactly isomorphism classes of rigidified pairs
  here: the universal equality O_T = q_* O_(C_T) in Picard splitting identifies the
  units on C_T with those on T. Consequently any two trivializations along P_T
  differ by a unique scalar automorphism of the line module, and isomorphisms of
  normalized underlying modules can be adjusted uniquely to preserve trivializations.
  This argument works for nonreduced and disconnected T as well as empty T. It is
  the existing `picardFunctorNormalized` encoding used in sk-prop-picard-pic-split,
  and Milne gives the rigidified-pair description explicitly on printed p.91.
  Since normalization and degree membership are subfunctors, pullback of M along
  every a belongs to the displayed target of the bijection.
- O(-P): the output `N : C.Pic` has its representative isomorphic to `P.ker.toModules`.
  This ties N to the point's ideal and therefore to O(-P), rather than leaving a
  free Picard class. Multiplication in Pic is tensor product, so `N ^ r` is O(-rP).
- Pointed Abel morphism: `fP : Over.mk f ⟶ J` and `IsClosedImmersion fP.left`.
  On every test scheme T and map Q to C, `pullback.lift Q.left (𝟙 T.left) Q.w`
  is the graph of Q in C_T. Its kernel ideal's dual is O(graph Q). The class `LQ`
  is tied by an actual representative isomorphism to that dual; the displayed
  `eJ.homEquiv (Q ≫ fP)` equality classifies `LQ * pr_C^* N`, namely O(Q-P).
  This specifies the morphism on all test schemes, including its scheme structure.
- Every integer 0 <= r <= g: `∀ r : ℕ, r ≤ g → ...`, so r=0 is included.
- Symmetric power/divisor scheme: `H : Over (Spec k)` and
  `eH : (hilbertPresheaf f r).RepresentableBy H`. This is precisely the recorded
  Hilbert scheme of effective degree-r divisors, not a Cartesian power or a point set.
- Isomorphism Pic^r to J: `τ : (picardFunctorDegree f (r : ℤ)).obj ≅
  (picardFunctorDegree f 0).obj`, followed by the fixed eJ. Its action is specified
  on every degree-r presheaf class by tensoring with `pr_C^* (N ^ r)`.
  Fppf-local surjectivity of sheafification makes this prescription determine the
  entire sheaf map. It is therefore the stated tensor-translation isomorphism on
  functors, hence the corresponding representing-scheme isomorphism, not just a
  bijection on k-points.
- Abel morphism `a : H ⟶ J`: on every `u : T ⟶ H`, its class is τ of the class of
  O(D), where `D = eH.homEquiv u`. The witness L is tied to `D.val.toModulesᵛ`.
  Thus it is exactly D maps to O(D-rP), with the canonical divisor-to-Picard
  interface and the same dual-ideal description as `exists_hilbertToPicardMorphism`.
- W_r: `a.left.image`, Mathlib's scheme-theoretic image, with inclusion `imageι`
  and canonical factor map `toImage`. The assertion is `IsIntegral a.left.image`.
- Dimension: `topologicalKrullDim a.left.image = (r : WithBot ℕ∞)`.
- Birationality of the specified factor map: `b : H.left.PartialIso a.left.image`
  together with `b.iso.hom ≫ b.target.ι = b.source.ι ≫ a.left.toImage`.
  The existing PartialIso includes dense source and target opens. The equation
  forces the open isomorphism to restrict the actual Abel factor map.
- W_g=J scheme-theoretically: `r = g → IsIso a.left.imageι`. The canonical closed
  image inclusion is an isomorphism, so this is equality as a closed subscheme,
  not just equality of underlying sets.
- W_(g-1) effective Cartier: `r = g - 1 → a.left.ker.IsInvertible`, the recorded
  effective Cartier ideal predicate, applied to the very ideal defining W_r.
- Last image-identification clause: the all-T formula for τ and the all-T formula
  for a state that a is the composite of Hilbert-to-Picard with the specified
  Pic^r-to-J isomorphism. Since W_r is its canonical scheme image, the effective
  divisor image under that isomorphism is precisely W_r with its scheme structure.

Dependency declarations read and used:

- `Field` (Mathlib.Algebra.Field.Defs), `IsAlgClosed` (Mathlib.FieldTheory.IsAlgClosed.Basic).
- `IsCurve`, `IsConnectedCurve`, `Scheme.Hom.genus` (WeilConjectures.AlgebraicGeometry.Curve).
- `IsHProjective` (WeilConjectures.AlgebraicGeometry.Morphisms.Projective).
- `IsJacobian` and `IsJacobian.represents` (WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian).
- `Scheme.Modules.IsInvertible` (WeilConjectures.AlgebraicGeometry.Modules.Invertible),
  and `Scheme.Pic`, `Scheme.Pic.map`, `Scheme.Pic.eq_iff_nonempty_iso`
  (WeilConjectures.AlgebraicGeometry.PicardFunctor).
- `hilbertPresheaf_curve_representable`, `hilbertPresheaf_curve_points`, and
  `hilbertPresheaf_curve_add` (WeilConjectures.AlgebraicGeometry.Hilbert.Curve).
  Their representing functor is the `hilbertPresheaf` used in eH.
- `exists_hilbertToPicardMorphism` (Sheaf.AlgebraicGeometry.HilbertToPicardMorphism):
  its complete signature uses the dual ideal, fibrewise-degree membership, and
  sheafification/representing equivalences, as the statement here does.
- `Scheme.Divisor`, `Scheme.Divisor.degree` (WeilConjectures.AlgebraicGeometry.Curve.Divisor),
  `Scheme.Divisor.moduleOfSmoothConnectedCurve` (Sheaf.AlgebraicGeometry.DivisorModule).
  No replacement divisor or line-bundle definition is introduced. The proof import
  DivisorLineBundleAgreesSC is the existing bridge to the dual-ideal convention.
- `picardFunctor`, `picardFunctorNormalized`, `sectionBaseChange`, `baseChangeMap`
  (WeilConjectures.AlgebraicGeometry.Picard.Defs), and its closed splitting theorem
  `bijective_toPicardFunctor_picardFunctorNormalized` for the rigidified encoding.
- `picardFunctorDegree`, `picardSubfunctorDegree`, `IsPicardZeroMul`
  (WeilConjectures.AlgebraicGeometry.Picard.Jacobian).
- `Scheme.Hom.image`, `imageι`, `toImage` (Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme).
- `Scheme.IdealSheafData.IsInvertible`
  (WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible).
- `IsClosedImmersion` (Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion).
- `Scheme.PartialIso` (Mathlib.AlgebraicGeometry.Birational.Birational), including
  its dense-open fields, used rather than defining another birationality notion.

The proof imports retain the available recorded proof dependencies. Two new proof-only
DAG nodes, lem-sfb-abel-differential-boundary and lem-sfb-small-degree-divisor-sections,
have no Lean record yet and are cited in the proof docstring. The proof-only record
lem-per-regular-prime-divisor-local-equations points at a withdrawn module: its note
says the module was deleted on 2026-10-20, the local source is absent, and the prescribed
server `scompile.py --source Sheaf.AlgebraicGeometry.RegularPrimeDivisorLocalEquations`
answered `Module source unavailable`. Its import is therefore omitted; its proof use
is retained in the docstring. None of these unavailable proof-only declarations is
needed to state this item. No statement dependency has an unusable record.

Edge cases checked mathematically before writing, and again against the final signature:

- r=0 is quantified and the empty effective divisor gives the reduced origin W_0,
  dimension zero; N^0=1 makes the translation the identity degree component.
- r=g is included and the image inclusion, not merely its underlying function, is an isomorphism.
- g=1 gives g-1=0: the Cartier assertion applies to the reduced origin on the smooth
  one-dimensional Jacobian. No assertion about a positive-degree theta divisor is required.
- g=0 is excluded exactly by hgpos. C is nonempty by the given point and also by
  IsConnectedCurve; the statement does not accidentally admit zero-dimensional curves.
- Arbitrary empty, disconnected, nonreduced, and non-Noetherian test schemes T remain
  allowed. The degree and normalization conditions use the existing presheaf definitions.
- There is no characteristic assumption and no positive-characteristic exception.
- Universes are bound explicitly (`universe u`, `autoImplicit false`), with the same
  schemes-over-k size convention as the recorded Hilbert and Picard interfaces.

Searches for an existing exact statement (2026-10-24):

- msearch.py leansearch: `universal line bundle Jacobian Abel map symmetric powers`.
  Eight irrelevant symmetric-power/elliptic-curve hits; no general Abel theorem.
- msearch.py leanfinder: `The Abel map from symmetric powers of a smooth projective curve
  to its Jacobian is birational onto its image of dimension r and the theta divisor is Cartier`.
  Eight affine Weierstrass class-map and Jacobian-point hits; none states this node.
- msearch.py loogle: `AlgebraicGeometry.IsJacobian, AlgebraicGeometry.hilbertPresheaf,
  AlgebraicGeometry.picardFunctorDegree`. No hits; the remote index does not know
  the project-specific IsJacobian identifier. Direct source reads resolved these interfaces.
- msearch.py grep: `AbelMap|abelMap|IsBirational|birational`, AlgebraicGeometry.
  Found Mathlib Birational/Birational and its PartialIso; no general symmetric Abel theorem.
- rg in both project Lean roots for `rigidif|abelMap|AbelMap|abelMorphism|symmetricAbel|pointedAbel`:
  found the Picard.Jacobian Abel class/presheaf map and unrelated rigidified-space lines.
  The existing Abel class API supplies O(D), but has no embedding/image geometry assertion.
- `grep -rn` for this node id under WeilConjectures: no existing attachment.
- rg for the two proposed declaration names in Mathlib, WeilConjectures, Sheaf,
  and dag/lean_names_upstream.json: no collision.

No statement dispute or correction. The only source-record fault noticed is the unavailable
proof-only regular-prime-divisor module described above. The theorem has one named sorry;
the helper has complete data and no sorry. Server scompile passed both sandbox and library
module-mode compiles cleanly (15.0 s and 6.8 s), with no warnings.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
