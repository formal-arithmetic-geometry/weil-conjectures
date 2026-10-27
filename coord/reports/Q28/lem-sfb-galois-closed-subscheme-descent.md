## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.GaloisClosedSubschemeDescent states
lem-sfb-galois-closed-subscheme-descent in two theorems. No mathematical hypothesis,
conclusion or node text is changed. Both theorem proofs are `sorry`.
The helper closedSubschemeGaloisMap constructs the explicitly named semilinear map
sigma_X using the already recorded baseChangeMap; it has real data and no postponed proof.

Source read: Milne, Algebraic Groups (2017), Appendix A.64--A.66, printed pp.580--581,
and Proposition 1.54(b), printed p.22. A.65 specifies preservation of the defining
ideal, not just the support. Proposition 1.54(b) gives precisely the subgroup
consequence. The node's proof expands that consequence using faithful flatness,
so A.66's separated-target graph argument is not imposed as an extra hypothesis.

Hypothesis and clause correspondence:

- The field k is `{k : Type u} [Field k]`.
- The extension E/k is `{E : Type u} [Field E] [Algebra k E]`.
- Finite dimension is `[FiniteDimensional k E]`.
- Separable algebraic and normal are `[IsGalois k E]`: the class has precisely
  `Algebra.IsSeparable k E` and `Normal k E` as fields. The former includes algebraicity;
  the latter states that every minimal polynomial splits in E. Their full source
  signatures and documentation were read.
- A k-scheme is `X : Over (Spec (.of k))`. Finite type is
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`, the recorded convention.
- X_E is `pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E)))`.
  Its projection to X is `pullback.fst` with those arguments.
- `σ : E ≃ₐ[k] E` ranges over every k-automorphism of E.
  `closedSubschemeGaloisMap X σ` is baseChangeMap for Spec σ in Over (Spec k).
  Its construction uses σ.commutes to check that this map is over the base;
  by the definition of baseChangeMap its factors are the identity on X and Spec σ.
- The closed subscheme Z_E is its full defining quasi-coherent ideal sheaf
  `J : (pullback ...).IdealSheafData`. Mathlib constructs the associated closed
  immersion as J.subschemeι, and every closed immersion is identified with its
  defining ideal via Scheme.Hom.ker. This representation includes all nilpotents.
- Preservation as a closed subscheme is exactly
  `hJ : ∀ σ, J.comap (closedSubschemeGaloisMap X σ) = J`.
  IdealSheafData.comap is defined as the kernel of the pulled-back closed immersion;
  its comapIso identifies its subscheme with the corresponding fibre product.
- Existence and uniqueness are `∃! I : X.left.IdealSheafData, I.comap ... = J`.
  Thus equality is equality of closed subschemes, or equivalently of their ideal
  sheaves, exactly the convention made explicit in node proof steps 3 and 4;
  it is not equality of arbitrary choices of their source schemes.
- In the subgroup clause, `G : Grp (Over (Spec (.of k)))` is the k-group scheme.
  Its finite-type hypotheses are the same ones on G.X.hom. Bundling GrpObj as
  Grp introduces no extra condition and records the existing group structure.
- `((Over.pullback b).mapGrp.obj G).X`, with b the field-extension Spec map,
  is the actual base-changed group scheme, with its canonical transported operations;
  no arbitrary group structure on G_E is a parameter.
- `Z : Grp (Over (Spec (.of E)))`, together with its inclusion `i` and
  `[IsClosedSubgroupScheme i]`, is precisely the given closed subgroup scheme.
  The existing class extends the homomorphism and pointwise injectivity condition
  with IsClosedImmersion i.left. The hypothesis hZ is preservation of i.left.ker.
- The conclusion produces `(H : Grp (Over (Spec (.of k)))) (j : H.X ⟶ G.X)`
  with `IsClosedSubgroupScheme j`. Its full kernel ideal pulls back to i.left.ker,
  and every ideal I with this pullback equals j.left.ker. Thus the subgroup is
  the same unique closed subscheme from the first theorem. Uniqueness concerns
  closed subschemes, without incorrectly requiring literal equality of group data.

Dependency declarations used (source signature and docstring read):

- Mathlib.Algebra.Field.Defs: Field; Mathlib.Algebra.Algebra.Defs: Algebra,
  with algebraMap k E; Mathlib.FieldTheory.Separable: Algebra.IsSeparable.
- Mathlib.FieldTheory.Galois.Basic: IsGalois, whose normality field uses
  Mathlib.FieldTheory.Normal.Defs: Normal. IsGalois packages the exact two conditions.
- Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType, and
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact.
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions: the recorded fibre-product
  and morphism-base-change conventions; its upstream PicardFunctor supplies baseChangeMap.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- Mathlib.CategoryTheory.Monoidal.Grp: GrpObj and its bundled Grp;
  Mathlib.CategoryTheory.Monoidal.Cartesian.Over and Monoidal.Grp provide the actual
  base-change functor on group objects, Over.pullback.mapGrp.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: IsClosedSubgroupScheme,
  extending IsSubgroupScheme and IsMonHom, exactly as recorded for
  def-sc-group-scheme-subgroup. No dependency module or replacement definition is needed.
- Mathlib.AlgebraicGeometry.IdealSheaf.Basic and Functorial: Scheme.IdealSheafData,
  Scheme.Hom.ker and IdealSheafData.comap, which implement closed subschemes.

Stated proof dependencies are imported: the affine-ideal comap theorem through
WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine, localization and tensor
through Mathlib.RingTheory.Localization.BaseChange, and faithfully flat ideal contraction
through Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra. The other Mathlib proof matches
are exposed by these imports and the public ideal-sheaf imports.
lem-sfb-galois-stable-subspace-descent currently has neither a usable Lean record nor
mathlib_match and is a proof-only prerequisite, so no nonexistent module is imported.
Its role is explicitly documented in the first theorem's natural-language proof.

Edge cases checked before writing: E=k (trivial Galois group); empty X and empty/all
closed subschemes (the unit/zero ideal); arbitrary nonradical ideals, including infinitesimal
subgroups; characteristic dividing [E:k] (no averaging or invertible-degree hypothesis);
nonseparated X (no separatedness binder or affine-intersection assumption);
nonreduced test algebras in the subgroup condition (the existing definition quantifies
all commutative k-algebras). The empty closed subscheme cannot satisfy the subgroup
hypothesis for a nonempty group, as the identity must belong to the subgroup.
There is no restriction on characteristic, reducedness, smoothness, affineness or
commutativity of the group. All universes and variables are explicitly bound.

Searches for an existing statement:

- msearch.py leanfinder: "Galois invariant closed subschemes descend along a finite
  Galois field extension" returned 8 hits: invariant integral closures, fixed fields,
  IsGaloisGroup and transitivity on prime ideals. None constructs the descended subscheme.
- msearch.py leansearch with the same query returned 8 hits on invariant rings,
  Galois extensions and fixed fields; none is the assertion here.
- msearch.py loogle: "IsGalois, IdealSheafData" returned zero hits (IdealSheafData
  was not recognized by that service).
- msearch.py grep: "[Gg]alois|[Dd]escen", AlgebraicGeometry/IdealSheaf, returned 8
  occurrences of order-theoretic Galois connections, not field Galois descent.
- rg over lean/WeilConjectures and lean/Sheaf for Galois/closed-subscheme descent
  found Frobenius maps with a finite-field datum, unrelated fpqc morphism-property
  descent, and invariant closed-substack descent. None states this result.
- rg for the item id in lean/WeilConjectures and in dag/lean_names_upstream.json
  returned no match. Searches for all three new declaration names in Mathlib,
  WeilConjectures and Sheaf returned no match.
- The existing finite-field galoisMap is restricted to FiniteFieldDatum, so it
  cannot be used for arbitrary k and E. The helper here simply specializes the
  existing general baseChangeMap and is part of the explicit sigma_X notation
  of this node, not a second independent notion or an arbitrary semilinear map.

No statement dispute, correction, new node or dependency repair is needed.

Validation: scompile.py compiled both the sandbox and the final module name cleanly
with no warnings. An initial elaboration failure in the helper was repaired by
making the Over.mk projection explicit before the Spec composition calculation.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
