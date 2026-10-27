## Worker report

The module `Sheaf.Paper.GaloisLimitNerveFaces` states
`AlgebraicGeometry.ProEtale.galois_limit_nerve_faces` and
`AlgebraicGeometry.ProEtale.galois_limit_nerve_constant_cocycle`. Both proofs are
`sorry`; there are no definitions with postponed data, new nodes, dependency
repairs, or statement changes. Only the item's `lean` field changes.

Sources read: Stacks `fields.tex`, lemma-infinite-galois-limit (Tag 0BU2),
`algebra.tex`, lemma-tensor-products-commute-with-limits (Tag 00DD), and
`limits.tex`, lemma-directed-inverse-system-affine-schemes-has-limit (Tag 01YW).
The current blueprint was read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3). That paragraph concerns continuous-coefficient open direct image;
the detailed Galois coordinate expansion is the present node's eight proof steps.
All eight steps are carried in the main theorem's docstring.

Hypotheses and clauses, matched to Lean:

1. A field k and a specified separable closure Omega are `(k Ω : Type u)`,
   `[Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]`. The group is
   `Ω ≃ₐ[k] Ω` with Mathlib's Krull topology and multiplication by composition.
   Its q-fold power is `Fin q → (Ω ≃ₐ[k] Ω)`. Mathlib's
   `FiniteGaloisIntermediateField k Ω` indexes exactly the finite Galois
   intermediate fields, and `E ≃ₐ[k] E` is Q_E.
2. The finite-stage Omega-algebra isomorphisms are the binder `θ`. The tensor
   power `E^{⊗q}` is the actual Mathlib `⨂[k] _ : Fin q, E`, so the full
   tensor is `Ω ⊗[k] (⨂[k] _ : Fin q, E)`. The binder `hθ` is precisely the
   stated pure-tensor formula: `((List.ofFn g).take (j.val + 1)).prod` is
   g_1 ... g_{j+1}, and coercion from E to Omega follows its application.
3. Compatibility under E <= F is `hθcompat`. Its left side includes each
   tensor entry in F. Its right side restricts each automorphism using
   `finGaloisGroupMap (homOfLE h).op`. Checking pure tensors is equivalent
   to the square of algebra homomorphisms commuting, by tensor extensionality.
   No tensor comparison is assumed in place of these specified formulas.
4. The first conclusion supplies `e q`, an Omega-algebra equivalence from
   `Ω ⊗[k] (⨂[k] _ : Fin q, Ω)` to
   `LocallyConstant (Fin q → (Ω ≃ₐ[k] Ω)) Ω`. Its first conjunct fixes its
   pure-tensor value by the same cumulative formula. Thus it is the canonical
   tensor identification, not merely some abstract ring isomorphism.
5. The finite product diagram and its colimit are given by `D`, `o`, and `ι`
   for each q. `o E` identifies `D.obj E` with the actual product Omega^{Q_E^q}.
   The next formula fixes `D.map` to precomposition by restriction, and the
   formula for `ι.app E` fixes the cocone to pullback by G^q -> Q_E^q.
   `Nonempty (IsColimit (Cocone.mk _ ι))` expresses the filtered colimit
   identification with LC(G^q,Omega). Together with `e`, this states both
   consecutive canonical algebra identifications. The naturality of `ι` is
   part of its type, rather than an omitted condition on a family of maps.
6. `Nonempty (IsLimit (Scheme.Spec.mapCone ...))` states the corresponding
   scheme inverse limit: the displayed cocone is forgotten to commutative
   rings, made opposite, and mapped through Spec. Its stages are the spectra
   of the finite product rings in (5), hence the finite disjoint unions via
   `sigmaSpec`; these are not products of schemes. Their maps are fixed by
   the restriction formula in (5).
7. The finite-map clause quantifies over `(A : Type v) [Fintype A]` with a
   discrete topology and `f : C(G^q,A)`, then gives E and fE with the exact
   restriction-factorization equality for every g. It includes the empty
   finite codomain; every finite type admits a Fintype, so this is all finite
   discrete sets, with an independent codomain universe.
8. `r q` identifies the actual scheme `Arrow.cechNerve.obj (op ⦋q⦌)` of
   Spec Omega -> Spec k with the spectrum of the tensor algebra. `c q`
   identifies Spec LC(G^q,Omega) with the dependency's actual test object
   `((profiniteToProEtOf (Spec (.of Ω))).obj (Profinite.of ...)).left`.
   `s q` is the composite coordinate identification: the equality involving
   `c.inv`, `Spec.map e`, and `r.inv` fixes this composite exactly.
9. The two formulas for `c.hom` followed by the projections of the test-object
   pullback normalize it on the Omega structure map and on LC(G^q,Z).
   They use `LocallyConstant.constRingHom` and
   `LocallyConstant.mapRingHom (Int.castRingHom Ω)` respectively. Thus `c`
   is the canonical identification of the recorded test object, not an
   unrelated isomorphism between abstract affine schemes.
10. The formulas for `r.inv` followed by vertex zero and vertex `j.succ`
    fix all tensor inclusions: `Algebra.TensorProduct.includeLeft` and
    `includeRight.comp (PiTensorProduct.singleAlgHom j)`. The Omega structure
    is the zeroth factor. In conjunction with the normalization of `e`, these
    are equalities of scheme morphisms, not a point-only characterization.
11. The formula quantified over a commutative ring B, `x : Ω →+* B`, g and
    `j : Fin (q+1)` explicitly gives the vertex as
    `Spec.map (x.comp (cumulativeProduct j).toRingHom)`. Its left side starts
    with `Spec.map (x.comp (LocallyConstant.evalRingHom g))` and uses `c` and
    `s`. Consequently the ring-map convention is x composed with g, while
    the scheme-point convention is Spec(g) composed with t, exactly in the
    specified order. Rings and schemes here have the ambient universe u.
12. `F n m α` is a genuine k-algebra homomorphism between the LC rings for
    every simplex map `α : [n] -> [m]`. Its evaluation formula acts on the
    value by the old cumulative product at `α(0)`. Its new increment at j
    is p_{α(j)}^{-1} p_{α(j+1)}. For the first face `α = δ 0`, this gives
    `g 0 (f (fun j => g j.succ))`: the base moves to x composed with g_1.
    For `δ i` with 0 < i < q it multiplies adjacent increments g_i g_{i+1};
    `δ q` drops the last increment. In particular the first face is only
    k-linear on coefficients and is not asserted to be Omega-linear.
13. For `α = σ i`, the same formula repeats selected cumulative vertex i,
    so that precisely the identity increment is inserted after the first i
    increments. This includes both endpoints and the q=0 diagonal.
    The next conjunct equates `Spec.map F` (transported by `c`) with the
    actual `Arrow.cechNerve.map α.op` (transported by `s`). All faces and
    degeneracies are thus specified as scheme morphisms, and the simplicial
    identities are inherited from that same Cech nerve.
14. On degree two the final conjunct says that the three pullbacks of f
    satisfy `F δ1 f = F δ2 f * F δ0 f` if and only if
    `f(gh) = f(g) * g(f(h))`. The faces select 02, 01, 12 respectively.
    This is the scalar structure-ring version of the moved-base cocycle;
    the `g` action is retained. For identifications from the later fibre
    to the earlier fibre, multiplication/composition is epsilon01 after
    epsilon12, in the order the node specifies.
15. The second theorem handles arbitrary constant coefficient monoids A,
    including invertible matrices and fibre automorphisms. It equates
    `c.comap multiplication = c.comap fst * c.comap snd` with
    `∀ g h, c (g*h) = c g * c h`. Thus the untwisted convention is asserted
    precisely for trivial action on the coefficient values. The general
    coordinate-ring and scheme-map formulas of the first theorem continue
    to retain the moved base; no general coefficient triviality is assumed.

Dependency declarations used and read:

- `def-pd-separable-closure`: module
  `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`, declaration
  `IsSepClosure.exists_intermediateField_mem`, whose docstring identifies the
  notion with Mathlib's `IsSepClosure`; that class is the binder used here.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: the recorded
  Mathlib matches in `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`,
  including `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`,
  `includeLeft`, `includeRight`, `productMap`, `productMap_apply_tmul`, and
  `ext`. The ordinary tensor product and both inclusions are used directly.
  `Mathlib.RingTheory.PiTensorProduct` supplies the actual finite tensor power,
  `tprod`, and `singleAlgHom`, not a private iteration of tensor products.
- `def-sfb-profinite-test-objects`: module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, declaration
  `AlgebraicGeometry.ProEtale.profiniteToProEtOf`. Its complete definition is
  the base change of `profiniteToProEt` along `toSpecZ X`; both projection
  normalizations in the theorem use that actual pullback.
- `def-pc-fibre-product`: the recorded Mathlib
  `CategoryTheory.Limits.pullback` with `pullback.fst` and `pullback.snd`.
  The test object uses this pullback and the nerve uses Mathlib's wide
  pullbacks; the tensor identification fixes every projection explicitly.

All proof dependencies are Mathlib leaves or the test-object module already
imported publicly. The factorization, affine pullback, and Spec-limit modules
are also imported as proof imports. Finite coproduct spectra are available
through the test-object module's import of `Mathlib.AlgebraicGeometry.Limits`.
The Galois/profinite and tensor Mathlib leaves are already public statement
imports, so no duplicate private imports are needed.

Edge cases checked:

- q=0: `Fin 0` is empty, its power of G is a singleton, the inner empty tensor
  is k, and the outer tensor is Omega tensor k, hence Omega. Empty products
  in both `hθ` and the normalization of `e` equal 1. There is no imposed
  nonempty set of increments.
- q=1: `δ 0` sends the constant a to g(a), whereas `δ 1` keeps a constant.
  `F` is a k-algebra map and deliberately not an Omega-algebra map.
- The zeroth degeneracy inserts the identity, including q=0; endpoint faces
  and degeneracies are covered by arbitrary simplex maps without inequalities
  that would exclude them.
- Trivial Galois group/already separably closed k, arbitrary characteristic,
  and finite closures are allowed. No nontrivial-group assumption appears.
- A=empty in finite factorization is allowed (there are no such maps from the
  nonempty G^q); the conclusion is not made vacuous by restricting the test
  codomain universe below that of the group.
- Zero rings B and noninjective base-point maps are permitted by `[CommRing B]`.
  Vertices are ring maps with no requirement that B be a field or k-algebra.
- The index type is the actual finite Galois intermediate fields of Omega,
  in its universe, rather than an independent arbitrary limit-index universe.

Searches actually run:

- `msearch.py ... leanfinder "The Cech nerve of a separable closure is locally
  constant functions on powers of its Galois group with twisted first face"`:
  eight hits, including `InfiniteGalois.finGaloisGroupFunctor_map_proj_eq_proj`,
  `Profinite.exists_locallyConstant_finite_aux`, general Cech nerves, and
  constant group-action models; no exact match.
- `msearch.py ... loogle "Arrow.cechNerve, InfiniteGalois, LocallyConstant"`:
  zero hits, unknown identifier `Arrow.cechNerve`. Source inspection located
  the fully qualified `CategoryTheory.Arrow.cechNerve`.
- `msearch.py ... grep "cechNerve|piTensorProduct|finGaloisGroup" FieldTheory`:
  five Galois/profinite hits, supplying finite restriction and its diagram.
- `msearch.py ... leansearch "separable closure Galois group locally constant
  functions tensor product Cech nerve face maps"`: eight separable-closure
  hits, including `IsSepClosure.isGalois`; no limit-and-face theorem.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for Galois/Cech, Galois/nerve, this node id,
  and the two chosen names: no existing declaration of this full statement.
  Source inspection found `AlgebraicGeometry.Scheme.GaloisCech`, which treats
  finite Galois covers in homogeneous coordinates, and the related parent
  module `Sheaf.Paper.FieldSeparableCechCoordinates`. The parent only gives
  the scheme identification and point formula, without the finite-stage
  colimit or actual LC ring maps; it is not an exact match. It is downstream
  of this node, so it is not imported to justify this prerequisite.
- Further direct Mathlib searches located `PiTensorProduct.singleAlgHom`,
  `LocallyConstant.evalRingHom`, `constRingHom`, `mapRingHom`,
  `CommAlgCat.of`, `Cocone.op`, and the Spec/finite-coproduct interfaces.

Validation: `scompile.py Q139 lem-sfb-galois-limit-nerve-faces` compiled the
complete delivered module both in its isolated sandbox test and under its
library name. The successful run reported 24.2 s and 12.3 s respectively,
with no errors or warnings. The initial attempt required one elaboration fix:
`@id` makes the constant-functor codomain explicit before LC evaluation.
No proof was filled during that repair. Every declaration variable and universe
is bound explicitly and `autoImplicit` is disabled. All lines are <=100 columns.

## Second reading by Q139

Single-worker reread before maintainer independent review (no second agent was
started, as required by the dispatcher). With the JSON and Lean file open, I
checked the finite-stage hypotheses (`θ`, `hθ`, `hθcompat`), both algebra
identifications (`e` plus `IsColimit`), the inverse scheme limit (`IsLimit`),
the finite-map factorization, the test-object identification, every vertex
projection, and every simplex map. The explicit normalizations for `r` and `c`
ensure these are canonical constructions, rather than arbitrary chosen
isomorphisms. The arbitrary-simplex formula includes the first-face action on
Omega, so it does not incorrectly make the first face Omega-linear. The triple
convention uses δ1 = 02, δ2 = 01, δ0 = 12 and retains g on the last factor.
The separate constant-coefficient theorem allows all monoids and gives the
untwisted order c(g)c(h). The only compiler-driven change was the explicit
constant-functor codomain cast described above; no mathematical correction or
clause omission was found. The original node statement and dependencies remain
unchanged.
