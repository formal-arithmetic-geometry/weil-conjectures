## Worker report

The module `Sheaf.AlgebraicGeometry.AffineCellPicardProduct` states
`AlgebraicGeometry.affineCellPicardProduct`, with its proof `sorry`.
It states the existing node without correction. There are no new definitions,
new nodes, or dependency repairs. No repair note exists for this item.

Clause-by-clause correspondence:

- The algebraically closed field is `F : Type u`, `[Field F]`, `[IsAlgClosed F]`.
  No restriction on characteristic is imposed.
- The schemes over F are `X T : Scheme.{u}` with structure maps
  `f : X ⟶ Spec (CommRingCat.of F)` and `g : T ⟶ Spec (CommRingCat.of F)`.
- Smoothness, properness and geometric integrality of X are precisely
  `[Smooth f] [IsProper f] [GeometricallyIntegral f]`. Properness includes
  separatedness and finite type; those are not additional assumptions.
- The open subscheme is `U : X.Opens` with its canonical open immersion `U.ι`.
  `hU : Dense (U : Set X)` means that its closure is all of X.
- `d : ℕ` includes zero. The isomorphism `cell` identifies `U.toScheme` with
  `AffineSpace (ULift.{u} (Fin d)) (Spec (CommRingCat.of F))`.
  `hcell` explicitly says this is an isomorphism OVER F. `ULift` merely places
  the finite coordinate index in the scheme universe, as the recorded
  def-sbc-affine-space Mathlib match requires.
- Smoothness, geometric integrality, separatedness and finite type of T are
  `[Smooth g] [GeometricallyIntegral g] [IsSeparated g]`
  `[LocallyOfFiniteType g] [QuasiCompact g]`. Finite type is the conjunction of
  the latter two classes, not just the first. Mathlib's geometric-integrality
  class quantifies over field-valued base changes and includes nonemptiness
  through integrality of every such fibre.
- The Picard groups are the existing `X.Pic`, `T.Pic`, and `(pullback f g).Pic`.
  Their abelian group structure is `Scheme.Pic.instCommGroup`, with tensor
  product as multiplication. For two abelian groups the finite direct sum
  is the product, so `(X.Pic × T.Pic) ≃* (pullback f g).Pic` is exactly the
  asserted abelian group isomorphism in multiplicative notation.
- The first conjunct fixes its value on EVERY pair `(M,N)` to
  `Scheme.Pic.map (pullback.fst f g) M * Scheme.Pic.map (pullback.snd f g) N`.
  This is the class of the external tensor product, rather than an unspecified
  group isomorphism. `Pic.map` is defined using ordinary module pullback.
  The imported `tensorOrdinaryPullbackIso` identifies that pullback with the
  dependency's tensor-formula pullback. `Pic.mul_def` and `Pic.mulIso` identify
  multiplication with the tensor product of representatives. Thus the class
  formula is precisely the node's tensor-pullback formula.
- The final conjunct quantifies over `t₀ : Spec F ⟶ T` with
  `ht₀ : t₀ ≫ g = 𝟙 _`, exactly an F-rational point of T, and over arbitrary
  module sheaves H on the product and L on X with `H.IsInvertible` and
  `L.IsInvertible`.
- The restriction hypothesis is `Nonempty (... ≅ L)`, using tensor pullback
  along the actual `pullback.lift (𝟙 X) (f ≫ t₀) ...`. Its two components
  are id_X and f followed by t₀, so it is x ↦ (x,t₀). The proof argument of
  `pullback.lift` is just the category equality forced by ht₀; it introduces
  no new assumption, helper theorem or unspecified map.
- The conclusion supplies `N : T.Modules` with `N.IsInvertible` and an
  isomorphism `H ≅ tensorPullback(p_X)(L) ⊗ tensorPullback(p_T)(N)`.
  Both pullbacks here use the dependency's actual tensor construction.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed` (every polynomial splits,
  equivalent to every nonconstant polynomial having a root). No algebraic
  closure of a smaller field is needed in this statement.
- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Scheme.Hom`, and `Scheme.Opens`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `IsProper`.
- Mathlib.AlgebraicGeometry.Geometrically.Integral: `GeometricallyIntegral`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`; using the
  canonical open-subscheme inclusion `U.ι` requires no additional binder.
- Mathlib.AlgebraicGeometry.AffineSpace: `AffineSpace`, `AffineSpace.over`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact`;
  Mathlib.AlgebraicGeometry.Morphisms.Separated: `IsSeparated`.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `Scheme.Modules.IsInvertible`, the Zariski locally rank-one predicate,
  and the scheme-module tensor product. These are publicly available through
  WeilConjectures.AlgebraicGeometry.Picard.Group.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction:
  `Scheme.Modules.tensorPullbackSectionAdjunction` and its public upstream
  WeilConjectures.AlgebraicGeometry.TensorPullback: `Scheme.Modules.tensorPullback`.
- WeilConjectures.AlgebraicGeometry.PicardFunctor: `Scheme.Pic`, `Scheme.Pic.map`;
  WeilConjectures.AlgebraicGeometry.Picard.Group: `Scheme.Pic.instCommGroup`,
  `Scheme.Pic.mul_def`, `Scheme.Pic.mulIso`.
- Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent:
  `Scheme.Modules.tensorOrdinaryPullbackIso`.

The existing landed nodes `def-sc-picard-group`, `lem-sc-pic-group` and
`def-weil-pbc-tensor-pullback-ordinary-comparison` are added to stmt_deps to
record these existing notions/comparison. Their declarations and full source
interfaces were read. No notion is copied. Original dependencies are retained.

All recorded proof-dependency modules are imported, using plain imports for
proof-only material. In particular the regularity, rational-point density,
affine-space line-triviality and divisor dictionary modules are imported.
The proof dependencies `lem-sfb-smooth-integral-fibre-vertical-divisors`,
`lem-sfb-integral-pullback-geometric-flat-open`, and
`lem-sfb-smooth-generic-trivial-line-descent` currently have no Lean record or
Mathlib match, and are proof-only; they are cited in the complete nine-step
proof docstring but create no missing object in this statement. They can be
imported when their statements land. No theorem from those nodes is assumed
as a binder. The regular divisor dictionary is currently recorded for spaces;
this statement needs none of its interface in its signature.

Source check: read Stacks chow.tex lemma-restrict-to-open (02RX),
lemma-pullback-affine-fibres-surjective (02TT), and the section identifying
codimension-one Chow classes with divisor classes, together with divisors.tex
lemma-local-rings-UFD-c1-bijective (0BE9). Read the latest blueprint's
sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md. This is an auxiliary
product Picard statement, not that unit's own six-functor statement. The module
docstring retains the full node proof: regularity and rational points;
regular integral product; affine-cell product; separated Noetherian schemes;
generic-fibre descent; boundary divisor pullback; homomorphism and surjectivity;
injectivity via two rational sections; prescribed fibre restriction.

Edge cases checked mathematically before writing:

- d=0 is included by Fin 0; the affine zero-space cell and its origin are valid.
  A nonempty dense zero-dimensional cell in the given integral proper X
  forces the expected point case; the isomorphism reduces to Pic(T).
- Empty X or T is excluded by the stated geometric-integrality hypothesis,
  not by a newly added nonempty assumption. U cannot be empty because it is
  isomorphic to affine space over a nonzero field and is dense.
- T=Spec F reduces to Pic(X) because Pic(F) is trivial. For X=P¹ and T an
  arbitrary smooth integral separated finite-type parameter scheme, the
  assertion gives the usual Pic(P¹×T)=Z⊕Pic(T).
- The final clause allows every rational point, every invertible H and every
  invertible L with the specified fibre isomorphism; no trivialization or
  uniqueness of N is imposed. Trivial H and L are included.
- F, schemes and finite coordinates use the same arbitrary universe u.
  There is no independently smaller test-field universe or extra equality
  between unrelated universes.

Searches (all on 2026-10-24):

- msearch.py leanfinder, query "Picard group of product smooth proper variety
  with dense affine space is direct sum of Picard groups": eight hits about
  ring Picard groups, including instCommGroupPic and CommRing.Pic.mk_tensor,
  with no scheme-product splitting statement.
- msearch.py loogle, query `"Pic", "prod"`: twelve hits about Finset products
  and noncommutative Pi coproduct homomorphisms; no match.
- msearch.py grep, query `Picard|picardGroup|PicardGroup` in AlgebraicGeometry:
  three Weierstrass comments about ring Picard groups; no match.
- msearch.py leansearch, query "Picard group of product with smooth proper
  variety having dense affine cell splits as tensor pullbacks": eight hits
  on ring Picard functor/tensor multiplication and scheme affine pullbacks;
  no product-Picard splitting theorem.
- rg in lean/WeilConjectures and lean/Sheaf for PicardGroup, picardGroup,
  Scheme.Pic, Picard/product names, and grep for this blueprint id: found the
  upstream Scheme.Pic, its group law and pullback, and general relative
  Picard/product-open results. These define required notions but do not state
  this affine-cell product splitting. No module contains this blueprint id.
- DAG search for Picard groups and isomorphism classes of invertible modules
  located def-sc-picard-group and lem-sc-pic-group, which are reused.

No STATEMENT-DISPUTED flag or mathematical node fault was found.
The final file compiles cleanly with the prescribed scompile.py server wrapper
in both sandbox and library module modes (1.9s and 2.2s respectively).

## Second reading by Q73

This is the worker's own second pass, not an independent-agent review: the
assigned brief explicitly forbids starting other agents and assigns independent
review to the maintainer. Reopened the node and the final file and compared each
clause against the correspondence above. In particular checked that hcell
preserves the F-structure, both finite-type components are present, the Picard
isomorphism has its external-tensor value specified, and the final clause is a
statement about actual invertible module sheaves with the specified L.
No mathematical mismatch was found. The final pass replaced the inline tactic
proof of the fibre inclusion's commutativity with the elementary category
identity as a term, and added the already-landed Picard and tensor-comparison
nodes to the statement-dependency record. No statement was corrected.
