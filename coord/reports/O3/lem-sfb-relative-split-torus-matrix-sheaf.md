## Worker report

The delivery states `AlgebraicGeometry.RelativeSplitTorus.matrix_sheaf_classification`
in `Sheaf.AlgebraicGeometry.RelativeSplitTorusMatrixSheaf`. Its only theorem has proof
`sorry`. Its helper definitions have real data and belong to the explicit model and
canonical comparisons already introduced in this node; no independent notion is added.
The node statement, dependencies, and nine-step proof are unchanged.

Source read: Milne, Algebraic Groups (2017), printed pp.232--234 (PDF pp.244--246),
Lemma 12.4, Remark 12.6, and Theorem 12.9(a). Milne works over fields and infers that
one orthogonal idempotent is 1; the node explicitly generalizes that coefficient
argument over rings by retaining the whole idempotent partition. Also read Stacks
`groupoids.tex`, `example-multiplicative-group`, Tag 022U. This gives precisely the
integer-model base-change construction and units on arbitrary test schemes. The
constant-sheaf identification uses the existing Tag 03P5 proof-dependency module.

Clause matching:

- Arbitrary scheme B: the family quantifies over every `B : Scheme.{u}`. There is
  no field, reducedness, connectedness, nonempty, quasi-compactness, or characteristic
  hypothesis. `r s n : ℕ` permit zero ranks.
- The prescribed relative group scheme: `LaurentAlgebra n` is
  `AddMonoidAlgebra (ULift.{u} ℤ) (Fin n → ℤ)`. Mathlib's actual Hopf instance has
  basis coproduct e^v to e^v tensor e^v, counit 1, and antipode e^(-v).
  `integerModel` is its spectrum, bundled as a commutative group object. `model B n`
  pulls this object back along `specULiftZIsTerminal.from B`, using
  `Over.pullback.mapCommGrp`. Its affine charts are therefore Spec A[Z^n], exactly
  the specified Laurent-algebra gluing, with those three base-changed structure maps.
  `integralProjection` is the pullback projection and `coordinate` pulls back the
  standard monomial `AddMonoidAlgebra.single (Pi.single i 1) 1` via `ΓSpecIso`.
- All W-points naturally equal n units: `p B n W` is a multiplicative equivalence
  from actual `Over B` morphisms to `Fin n → Γ(W.left, ⊤)ˣ`. The first conjunct
  fixes its value by the displayed coordinate function, and the second gives
  naturality for every `a : W ⟶ V` using the actual pullback of global functions.
  The multiplicative equivalence includes multiplication, identity, and inverse.
- Hom classification: `e B r s` is an equivalence from morphisms in
  `Grp (Over B)` to `LocallyConstant B (Matrix (Fin s) (Fin r) ℤ)`. Mathlib group
  morphisms preserve the unit and multiplication; inversion is automatic.
  `LocallyConstant` imposes open fibres for a discrete target, with no topology
  on the integer matrix type required.
- Monomial normalization: for every open `U`, fixed matrix `A`, and `f` whose
  exponent function is A on U (`hA`), and every test scheme W whose structural
  map has image in U (`hW`), the third conjunct asserts that the j-th unit of
  `x ≫ f.hom.hom` equals `∏ i, p ... x i ^ A j i`. Factoring through an open
  immersion is equivalent to the image condition. This fixes the correspondence
  on every test scheme, rather than just geometric points.
- Composition and identity: the fourth conjunct is `e (f ≫ g) b = e g b * e f b`,
  with rows indexed by the target rank; the fifth gives the identity matrix.
- Pointwise multiplication: the sixth conjunct supplies a morphism h whose actual
  underlying `Over` morphism is `f.hom.hom * g.hom.hom`, and whose matrix is the
  pointwise sum. Mathlib's scoped `MonObj` multiplication is exactly the product
  of the two output points through the target group law. Uniqueness follows
  from equality of underlying maps (and also from e being a bijection).
- Arbitrary base change: `β b n` is a group isomorphism from the actual pullback
  of the fixed model to the model over B'. The seventh conjunct specifies this
  comparison on every test scheme by `Over.mapPullbackAdj.homEquiv` and p, so it
  is the canonical comparison, rather than an arbitrary isomorphism.
  `changeHom` conjugates the actual pullback of f by these β isomorphisms. The
  eighth conjunct says its matrix at x is `e B r s f (b x)`.
- Automorphisms: the ninth conjunct gives `Aut (model B r).toGrp ≃
  LocallyConstant B (Matrix (Fin r) (Fin r) ℤ)ˣ`, namely locally constant maps to
  units of the integer matrix ring (GL_r(Z)), and fixes their underlying matrices
  to be those of the original Hom classification. Here the postfix units type
  belongs to the matrix target of `LocallyConstant`; it is not a choice of an
  unrelated automorphism parameterization.
- Rank zero: the tenth conjunct identifies the actual rank-zero group object
  with `Grp.trivial (Over B)`. Scheme equality in the informal presentation is
  represented by the canonical group-object isomorphism convention.
- Character sheaf: the last conjunct supplies an `AddCommGrpCat.{u+1}`-valued
  presheaf H on `B.Etale`, its actual small-etale sheaf condition hH, and objectwise
  equivalences q with the actual U-group Hom sets from ranks r to 1. The restriction
  equation for every etale morphism uses `changeHom` with the same canonical β.
  The addition equation sends addition in H to multiplication of characters.
  The sheaf isomorphism φ is from Mathlib's actual `constantSheaf` of the lifted
  additive group `Fin r → ℤ`. Its last equation fixes the image under the actual
  sheafification unit of every constant vector v to the constant row matrix v.
  Thus this is the natural constant character sheaf, including its abelian-group
  law and the specified monomial constants. The one-universe lift is the existing
  convention for sheafification on the small etale category, and does not restrict B.

Recorded statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  these are the recorded `def-pc-scheme` declarations.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and
  `Scheme.Etale`, with the etale over-category and jointly-surjective coverings.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  explicitly sheafification of the constant presheaf, not a replacement universal property.

Proof-dependency sources read and imported: `pullback`, `pullback.fst/snd` from
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (available through the
public affine/limits imports); `Spec` and `Spec.map` from Scheme;
`ΓSpec.locallyRingedSpaceAdjunction` from GammaSpecAdjunction (through Group.Affine);
`pullbackSpecIso` from Pullbacks (through Group.Affine);
`Algebra.TensorProduct.productMap`, its generator formula and `ext` from tensor
Basic/Maps; `Scheme.Cover.glueMorphisms`, its restriction and uniqueness lemmas from
Gluing; `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen` from
Spectrum.Prime.Topology; `Scheme.constantSheaf_sets_representable` and its helper
from `Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable`; and
`coproductCopiesMorphismsClopen` from its recorded Sheaf module. The last two
modules and the proof-only algebra/gluing modules have ordinary imports.

Edge cases checked mathematically before writing:

- r=0 and s=0 give unique empty matrices and Hom sets; empty products are 1.
  GL_0(Z) is the unit group of the one-element empty matrix ring. The zero-rank
  model is the base itself as a group object, up to its unique isomorphism.
- B empty (including the zero-ring affine chart) gives empty relative models,
  singleton Hom and locally constant function sets, and the unique constant sheaf
  over the empty site. No point or nonzero-ring hypothesis is used.
- A disconnected base can assign different matrices to different clopen pieces.
  Orthogonal coefficient idempotents account for exactly these possibilities.
- For nonreduced A, the coefficient equations c_v^2=c_v and c_v*c_w=0 still hold;
  nilpotent coefficients do not provide extra homomorphisms.
- An unbounded locally constant function on a non-quasi-compact base is allowed;
  neither the statement nor the construction imposes a finite image globally.
- Base change includes the identity, open inclusions, non-flat maps, and maps from
  the empty scheme. Every comparison is fixed through the same p and β families.

Searches actually run:

- `msearch.py ... leanfinder "Homomorphisms between split tori over an arbitrary
  scheme are locally constant integer exponent matrices"`: eight hits, chiefly
  `AffineSpace.homOverEquiv` and coordinate maps. These concern additive affine
  space and do not classify multiplicative group morphisms.
- `msearch.py ... leansearch "Group scheme morphisms between split multiplicative
  tori over a scheme are locally constant integer matrices"`: eight hits including
  `Scheme.Hom`, `LocallyConstant.instGroup/instCommGroup`, etale and smooth morphisms.
  None is the relative torus classification.
- `msearch.py ... loogle "AlgebraicGeometry, Grp"`: the query reported the namespace
  identifier AlgebraicGeometry unknown, and yielded no usable search. A corrected
  query `LocallyConstant.comap` returned twelve hits including `comap`, its evaluation
  and composition lemmas; these give general locally constant pullback, not the
  torus equivalence.
- `msearch.py ... grep "splitTorus|SplitTorus|diagonalizable" AlgebraicGeometry`
  and `... grep "torus|Torus|group.like" AlgebraicGeometry`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures` for this node id gave no hits. Searches of
  `lean/Sheaf`, `lean/WeilConjectures`, and `dag/lean_names_upstream.json` for
  relative split torus names found no classification.
- Broader project/DAG searches found and read `RelativeTorus.lean`,
  `GroupScheme/SplitTorusOverRing.lean`, `ToriMultiplicativeType.lean`,
  `DiagonalizableGroup.lean`, and `StandardGroupSchemes.lean`. The relative-torus
  file defines only the units functor and its local splitting condition. The
  ring split-torus file defines a recursively parenthesized product of G_m over
  Spec R, with no arbitrary-base coordinate model or Hom classification. The
  field files require Field. The present explicit arbitrary-base Laurent model
  uses Mathlib's same Hopf and group-object definitions, not a second notion of
  group scheme or a new local-splitting predicate.

Validation: prescribed `scompile.py O3 lem-sfb-relative-split-torus-matrix-sheaf`
compiled both its sandbox module and final library module cleanly (4.3 and 4.7 s).
An initial coordinate used `Finsupp.single` rather than Mathlib's bundled
`AddMonoidAlgebra.single`; that typing error was repaired before the clean run.
All variables/universes are explicit; auto-implicits are disabled; all lines are
at most 100 characters. There are no statement disputes or node corrections.

## Second reading by O3

This is the dispatcher's single-worker self-check; the maintainer supplies the
independent reading. Re-read the node and final source side by side. The ranks,
base generality, Hopf model, test-scheme points and naturality, Hom bijection,
openwise monomial equation, multiplication order for composition, identity,
pointwise product/addition, normalized arbitrary base change, GL_r normalization,
rank zero, and constant abelian character sheaf all have the counterparts detailed
above. In particular the constant section condition uses the sheafification unit,
not an unspecified map from constants. The character restrictions are the actual
base-changed homomorphisms, not an arbitrary presheaf with equicardinal fibres.
No mismatch was found in this reading. The coordinate-construction typing repair
was already compiled. No dependency node or existing live source was modified.
