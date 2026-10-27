## Worker report

`Sheaf.AlgebraicGeometry.SplitLatticeTorusProjection` states the complete assigned node as
`AlgebraicGeometry.split_lattice_torus_projection`, with one `sorry` proof. There are no
new definitions, new nodes, dependency-node changes or mathematical statement corrections.

Hypothesis and clause correspondence, using A = AddMonoidAlgebra k L in this explanation
(the Lean signature writes the actual terms throughout):

| Node text | Lean rendering |
| --- | --- |
| k a field | `(k : Type u) [Field k]` |
| L an abelian group | `(L : Type u) [AddCommGroup L]`; the canonical integer module structure is Mathlib's existing one |
| finite integral basis b_1,...,b_r, r >= 0 | `(r : ℕ) (_b : Module.Basis (Fin r) ℤ L)`; the underscore only prevents the unused-binder warning in this stage-2 statement |
| A = direct sum of ke^l, multiplication adds exponents | `AddMonoidAlgebra k L`, whose `single l c` denotes c e^l, with convolution multiplication |
| T = Spec A over k | `Spec (.of (AddMonoidAlgebra k L))` with structural map `Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k L)))` |
| arbitrary k-scheme Y | `(Y : Scheme.{u}) (y : Y ⟶ Spec (.of k))`; no finiteness, separatedness, nonemptiness or reducedness hypothesis |
| projection T times_k Y to Y is smooth | first conjunct, `Smooth (pullback.snd ... y)` |
| section induced by e^l -> 1 | existential `s` with `s ≫ pullback.snd ... y = 𝟙 Y` and `s ≫ pullback.fst ... y = y ≫ Spec.map ...`; the latter uses `(AddMonoidAlgebra.lift k k L 1).toRingHom`, the lift of the constant-one monoid homomorphism |
| projection surjective on points | `AlgebraicGeometry.Surjective (pullback.snd ... y)`, Mathlib's class for surjectivity of the underlying point map |
| T smooth over k | `Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A)))` |
| each field extension K/k | `∀ (K : Type (max u v)) [Field K] [Algebra k K]`; no algebraicity, separability or characteristic restriction |
| canonical K-algebra isomorphism A tensor_k K to K[L], e^l tensor c -> c e^l | existential `@AlgEquiv K (A ⊗[k] K) (AddMonoidAlgebra K L) ... (Algebra.TensorProduct.rightAlgebra (R := k)) ...`, with `∀ l c, e (single l 1 ⊗ₜ[k] c) = single l c`; these monomial tensors span, so the formula specifies the canonical isomorphism, rather than an arbitrary uncharacterized equivalence |
| K[L] an integral domain | `IsDomain (AddMonoidAlgebra K L)` in the same universally quantified conjunct |
| every reduced commutative k-algebra R, including zero | `∀ (R : Type (max u w)) [CommRing R] [Algebra k R] [_root_.IsReduced R]` |
| R tensor_k A reduced | `_root_.IsReduced (R ⊗[k] AddMonoidAlgebra k L)` |
| reduced Y implies reduced product | `IsReduced Y → IsReduced (pullback ... y)`; the earlier smoothness and section clauses apply also to nonreduced Y |

All variables and universes are explicit; `autoImplicit` is false. The common universe u
contains the field, lattice and schemes, while the independently larger v,w allow larger
extension fields and reduced algebras. In particular the quantified test algebras cannot
accidentally be smaller than the base field. Any collection of these objects can be placed
in a common scheme universe; no algebraic condition or cardinal bound is imposed.

Dependency declarations read and used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullback existence.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`, the existing affine-local smoothness predicate.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`, whose sections are all reduced.
- Further Mathlib interfaces: `Module.Basis`, `AddMonoidAlgebra`, its universal `lift`,
  `AlgebraicGeometry.Surjective`, `TensorProduct`, `AlgEquiv`, and
  `Algebra.TensorProduct.rightAlgebra`. The last explicitly equips A tensor K with the
  K-algebra structure on its right factor, without a file-local instance or notation.
- Stated proof dependencies are retained as imports: first-order thickenings from
  `WeilConjectures.AlgebraicGeometry.Thickening`, reduced algebra base change from
  `Sheaf.RingTheory.GeometricallyReducedBaseChange`, and the domain theorem from
  `Sheaf.RingTheory.MonoidAlgebraDomainFraction`. The affine-reduced-iff proof dependency
  is already in the public signature dependency `Mathlib.AlgebraicGeometry.Properties`;
  the tensor-product definition is supplied by the tensor-product import.
- `lem-trf-lattice-torus-coordinates-action` has neither Lean record nor Mathlib match
  and is only a proof dependency, so it is documented in the complete proof plan but
  has no module to import. It is not needed to type this statement.

The theorem docstring reproduces the six accepted DAG proof steps, naming the dependencies:
Laurent charts and finite presentation; square-zero unit lifting; augmentation section;
scalar-extension inverse on monomials; domain and geometrically reduced base change;
and reduced affine charts covering the product. Nothing is proved here.

Source read: ILO PDF pages 110--112, printed pp.104--106, including Lemma 3.2.12(i), its
proof and 3.2.19. The smoothness statement in (i) allows arbitrary base schemes; the
characteristic-zero assumption in the desingularization application is not an assumption
of this elementary split-torus lemma. The DAG's expanded elementary proof handles that
distinction correctly. Read the current dependency signatures and docstrings, not only
their recorded names. The example CompactObject file is now withdrawn; I also read its
upstream replacement `WeilConjectures.CategoryTheory.CompactObject` and the node record.
No repair note exists for this item.

Edge cases checked before and after drafting: r=0 gives the empty basis and trivial L;
the group algebra then is k. Empty Y is allowed and the section and surjectivity have empty
source and target. Reducible reduced Y is included, as no irreducibility is assumed.
R=0 is a commutative k-algebra and a reduced ring, and its tensor product is zero. Neither
positive characteristic (including characteristic two) nor inseparable K/k is excluded.
The algebra-isomorphism formula is on e^l tensor c, in the orientation A tensor K specified
by the node. All assertions remain valid in these cases. No STATEMENT-DISPUTED fault.

Searches actually run:

- `msearch.py leanfinder`: “The group algebra of a finite free abelian group over a field
  gives a smooth torus with identity section and reduced products”. Eight hits, including
  UnitAddTorus, torusMap and analytic tori, plus general free-module bases; none states
  this scheme-theoretic assertion.
- `msearch.py loogle`: `"AddMonoidAlgebra", "Smooth"`: zero hits.
- `msearch.py grep`:
  `(AddMonoidAlgebra|MonoidAlgebra).*(Smooth|IsReduced)|(Smooth|IsReduced).*(AddMonoidAlgebra|MonoidAlgebra)`:
  zero hits.
- `msearch.py leansearch`: “group algebra base change tensor product isomorphic group
  algebra over extension field smooth torus”: eight hits on general base change,
  tensor-product identifications and basis base change, no full match.
- `msearch.py grep`: `split_lattice_torus_projection|SplitLatticeTorusProjection`: zero hits.
- Direct `rg` of `lean/WeilConjectures` for the item id found no match; direct `rg` of
  upstream/project algebraic geometry, ring theory and algebra for group algebras, tori,
  augmentation, split lattice and candidate declaration names found the existing
  toric-realization and monoid-algebra ingredients and uses of the item, not this complete
  arbitrary-lattice statement. Exact-name search of `dag/lean_names_upstream.json` and
  both source roots found no collision. No existing toric-component specialization is
  substituted for the arbitrary finite-basis abelian group.
- Direct Mathlib source search found and read `AddMonoidAlgebra.scalarTensorEquiv` in
  `Mathlib.RingTheory.TensorProduct.MonoidAlgebra`: this is an available ingredient, with
  the opposite tensor orientation K tensor A. The theorem's formula states the required
  canonical A tensor K isomorphism and does not introduce a duplicate definition.

Compilation: only the prescribed `scompile.py` wrapper is used. The first module-mode
compile failed because `Sheaf.RingTheory.MonoidAlgebraDomainFraction` is a published legacy
non-module file; `scompile.py --source` confirmed that current server source. This file
uses the compatible legacy layout so that every stated proof dependency can stay imported,
without rewriting any dependency, omitting its import, or copying its declarations.

## Second reading by Q06

I reopened the JSON node and the complete Lean file for a separate clause-by-clause reading;
the maintainer's review is the independent reading, since the dispatcher prohibits starting
another worker. The table above records the correspondence actually checked. The first
version's module header was incompatible with the legacy proof dependency; only file layout
and import visibility were adjusted, with no change to the mathematical signature. I checked
that the section has both the identity second projection and the augmentation first
projection; bare existence of an arbitrary section would have missed the latter clause.
I checked that the scalar-extension isomorphism is over K, by the explicit right-factor
algebra structure, and that its monomial formula has coefficient c rather than algebraMap
of an unspecified coefficient. I checked that IsDomain belongs to K[L], that R tensor A
has the required order, and that reducedness of Y is an implication rather than a global
hypothesis. No node statement, dependency or proof-plan change was necessary.
