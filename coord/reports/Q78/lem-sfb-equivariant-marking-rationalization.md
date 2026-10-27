## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantMarkingRationalization` states
`AlgebraicGeometry.exists_equivariant_marking_rationalization`, with its only theorem proof
`sorry`. No statement correction is made. The accepted seven-step proof is reproduced in the
docstring, including the empty polynomial list and inseparable genus comparison.

The module also constructs two maps, without postponed data or proofs:
`EquivariantMarkingRationalization.fibreComponentι` is the existing vanishing-ideal
subscheme inclusion, and `normalizedFibreComponentToSpec` is the composite of the existing
normalization map, that inclusion, and the fibre projection. These are canonical maps used
by this statement, not new notions of component, normalization or genus. Their declarations
are listed in `lean.declarations`.

Source read: de Jong, *Families of curves and alterations* (1997), publisher PDF
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf, §§3.1--3.3, printed p.605,
and §3.6, printed p.608; also the definition of condition (2.1.6), p.601. The PDF's
§3.2 uses the reduced base change; this node explicitly takes its further normalization
as supplied by its accepted finite-normal-relative-curve-model prerequisite. The current
blueprint direct-image proof was read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`.
The node is an extracted prerequisite, not the unit's own statement.

Hypotheses, matched individually:

- A field k: `(k : Type u) [Field k]`.
- S and X integral: `(S X : Scheme.{u}) [IsIntegral S] [IsIntegral X]`.
- S is a k-scheme, projective and finite type: `p : S ⟶ Spec (.of k)`,
  `[IsHProjective p] [LocallyOfFiniteType p] [QuasiCompact p]`.
- Normal S and normal X: `hSnormal` and `hXnormal` require each local ring to be a domain
  and integrally closed, exactly the node's explicit convention.
- H-projective f and finite-type X/k: `[IsHProjective f]`,
  `[LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)]`. The composite gives the
  specified k-structure on X.
- Every geometric fibre is pure of dimension one: `hpure`, for every algebraically
  closed Ω and every `Spec Ω ⟶ S`, using the existing `Scheme.IsPureDimension 1`.
- C = X_K smooth and geometrically integral: the two instances on
  `pullback.snd f S.fromSpecFunctionField`. K and F are the actual generic stalks
  `S.functionField` and `X.functionField`. The K-algebra structure on F is supplied
  with `hKF`, which identifies its spectrum map with f at the generic point. This
  records the induced embedding, not an arbitrary field extension or an additional
  geometric assumption.
- M reduced finite étale closed in C: `M`, `i`, `[IsClosedImmersion i] [IsReduced M]`,
  and the finite and étale instances on `i ≫ pullback.snd f S.fromSpecFunctionField`.
- A finite group acting on k, X and S: `G`, `[Group G] [Finite G]`, and `σk, σX, σS`.
  `hk` expresses semilinearity on S; `hequiv` expresses equivariance of f and therefore
  semilinearity on X with its composite k-structure. `hMstable` preserves M after the
  generic-fibre inclusion. Since M is reduced, preservation of this closed set is
  preservation of its reduced induced closed subscheme. No faithfulness is required.
  Ring actions are inverse pullbacks of the scheme actions, as in the landed StalkAut
  and HighGenusEquivariantCover interfaces.

Conclusions, matched individually:

- B = K^G: the existential subfield B is characterized elementwise by the first iff.
- K'/K finite and Galois over B: E is a field with the K- and B-algebra structures,
  `IsScalarTower B S.functionField E`, both finite-dimensionality clauses, and
  `IsGalois B E`. This includes K as its specified algebra-map image.
- E receives every residue field of M: `∀ m : M, ∃ j : M.residueField m →+* E`.
  The displayed composition equation makes j a K-embedding for the canonical
  structure morphism of that residue field. A ring hom between these fields is injective.
- The exact group G': `β : G' →* G` and `σE : G' →* (E ≃+* E)` have injective pair map.
  The iff quantified over every `(g, τ)` says its image consists of precisely the pairs
  where τ fixes B and restricts to the given action on K. Thus this is a presentation
  isomorphic to the node's literal fibre-product group, with its actual two projections,
  rather than an arbitrary group surjection. `Function.Surjective β` is separate.
- N = Aut_K(E): the next iff identifies the image of `β.ker` under σE with precisely
  all ring automorphisms fixing K. Pair injectivity makes this identification injective
  as well. Multiplication is inherited from the two homomorphisms.
- E^N = K: the elementwise range iff for `algebraMap S.functionField E` uses this same
  kernel action and the specified field embedding.
- F' = F tensor_K E is a field finite separable over F: `IsField (TensorProduct ...)`,
  the existential field L, and `eL : TensorProduct ... ≃+* L`, with the pure-tensor
  formula and both scalar towers; `FiniteDimensional X.functionField L` and
  `Algebra.IsSeparable X.functionField L`. L is only a presentation of this very
  tensor product, with both inclusions explicitly determined.
- S' = Nor_E(S), X' = Nor_L(X): all conclusions use `S.normalizationIn E` and
  `X.normalizationIn L` literally. There are explicit local normality and integral
  clauses, S'/k H-projective and finite type, and X'/k finite type.
- Finite surjections S' → S and X' → X ×_S S': `IsFinite` and `Surjective` on the
  former normalization map and r. The equations for both projections of r identify
  its X-projection with `X.fromNormalizationIn L` and its S'-projection with q.
- The morphism X' → S': q commutes with both normalization maps and the specified
  generic maps `Spec L`, `Spec E`. It is H-projective and its every geometric fibre
  is pure one-dimensional.
- The smooth geometrically integral generic curve is C ×_K E: the smoothness and
  geometric-integrality clauses use q pulled back along the canonical `Spec E → S'`.
  `eC` identifies that fibre with the scalar extension of C; both displayed
  projection equations tie it to the original X-map and the E-structure. The finite
  normal-model theorem identifies this canonical `Spec E` with the generic spectrum
  of S'; using E therefore avoids an arbitrary identification of abstract function fields.
- The tensor action: σL's formula on `eL (TensorProduct.tmul ... z c)` is exactly
  `(g, τ)(z tensor c) = g(z) tensor τ(c)`, with the inverse-pullback ring action
  attached to σX. The actions τS, τX on the actual normalizations commute with q
  and their maps to S, X. Their equations on the normalized maps from `Spec E` and
  `Spec L` fix which lifts are meant, including on the constants.
- L^N = F: the elementwise range iff for `algebraMap X.functionField L` and σL.
- The reduced inverse image of M is a finite set of distinct E-rational points:
  `n : ℕ`, `a : Fin n → (Spec E ⟶ generic fibre)`, the section equations, pairwise
  disjoint ranges, and the pointwise iff identify its support with the actual pullback
  of i along the scalar-extension projection, transported by eC. The reduced inverse
  image is determined by this support; since M/E is étale it is already reduced.
  The final image equality expresses G'-stability on X'. No nonemptiness of M or Fin n
  is assumed; `n = 0` is allowed.
- Precise genus comparison: for every Ω and `s : Spec Ω ⟶ S'`, hF has precisely the
  two projections of the induced fibre map. Each Z' has a target component Z and a
  finite surjective map h between the reduced induced components. Its equation with
  the two component inclusions ties it to hF. Both fibres are over exactly the same Ω.
  Finite surjectivity onto the dimension-one target component implies h is nonconstant.
  The map hν commutes with their normalization maps; both normalized Ω-structures
  are explicitly smooth and proper and hν is an Ω-map. The nonconstant clause rules
  out factorization through an Ω-point of the target normalization. The inequality
  is the existing `Scheme.arithmeticGenus` with precisely those Ω-structures.
- Every lower bound b ≥ 0 is preserved: the last implication quantifies over `b : ℕ`
  and all geometric fibre components on the two sides, using exactly the same genus
  and normalization maps as the precise inequality. Nonnegative integers are ℕ.

Dependency declarations read and used (module → names):

- `Mathlib.Algebra.Field.Defs` → `Field`.
- `Mathlib.Algebra.Algebra.Defs` → `Algebra`, `algebraMap`.
- `Mathlib.AlgebraicGeometry.Properties` → `AlgebraicGeometry.IsIntegral`, `IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` → `LocallyOfFiniteType` and the
  recorded `QuasiCompact` conjunction for finite type.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective` → `IsHProjective`.
- `WeilConjectures.AlgebraicGeometry.FunctionField` → the integral-scheme clause
  reuses `Scheme.functionField` from Mathlib, as the dependency's docstring specifies;
  the product `functionFieldOfComponents` is not used for these integral S, X.
- `Sheaf.AlgebraicGeometry.PureDimension` → `Scheme.IsPureDimension`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` → `pullback`,
  `pullback.fst`, `pullback.snd` for the fibre-product and geometric-fibre nodes.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth` → `Smooth`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral` → `GeometricallyIntegral`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization` → `Scheme.normalizationIn`,
  `fromNormalizationIn`, `Hom.toNormalization`, `Scheme.normalization`, `fromNormalization`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite` → `IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` → `Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale` → `Etale`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` → `Scheme.arithmeticGenus`.
- The added already-landed dependency `def-weil-pbc-reduced-normalization`, module
  `Sheaf.AlgebraicGeometry.ReducedNormalization` → `Scheme.reducedNormalizationComponent`
  and its integral instance. Its source, statement, full definitions and docstrings were read.
  No dependency node is edited and no new definition node is needed.
- `WeilConjectures.AlgebraicGeometry.StalkAut` → `Scheme.functionFieldAut` supplies
  exactly the induced automorphisms on the generic stalks, rather than private copies.
- `Mathlib.FieldTheory.Galois.Basic` → `IsGalois`; the extension's fixed fields are
  written elementwise because the original action need not be faithful.

All stated proof dependencies have their modules imported (including the Mathlib
primitive-element, finite-morphism, proper-closed-image modules). The polynomial-envelope
proof node has no usable statement record in the read checkout; it is only a proof
prerequisite here, not required to type this statement, so no proof import is possible.
The geometric model and genus interfaces already available are reused.

Edge cases checked before writing and in the second pass: M empty (no residue-field
conditions, zero rational points), G trivial, nontrivial kernel of G acting on K, totally
nonfaithful actions, dimension-zero base, arbitrary characteristic, inseparable maps on
special-fibre components, b = 0 and b = 1, reducible and nonreduced geometric fibres,
and geometric points at nonclosed points. There is no flatness hypothesis, no restriction
to closed geometric fibres, no faithfulness condition, and no requirement that the special
fibres themselves be smooth. Scheme/field universe u is explicit; group universe v is
independent and G' has universe max u v, as does the fibre-product presentation.

Searches actually run:

- `msearch.py ... leanfinder "finite Galois extension splitting finite etale marking equivariant
  normalization relative curve genus"`: eight hits, including finite étale algebras over a
  field and fraction-field Galois actions; no theorem with this full statement.
- `msearch.py ... leansearch "finite Galois constant field extension rationalizes finite etale
  marking normalization relative curves"`: eight hits, on IsGalois and finite Galois
  intermediate fields; no full matching theorem.
- `msearch.py ... loogle "IsGalois, IntermediateField.fixedField, TensorProduct"`: zero hits.
- `msearch.py ... grep "equivariant.*marking|marking.*rational|normalizationIn|fixedField"
  AlgebraicGeometry`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` by the item id and marking/rationalization
  keywords found the related HighGenusEquivariantCover proof, not this statement.
  Its genus and action encodings were read and reused. Searches for the three proposed
  declaration names in Mathlib, WeilConjectures and Sheaf found no collision.
- Searched DAG records for `reducedNormalizationComponent`: found the already-landed
  `def-weil-pbc-reduced-normalization`; it is added to stmt_deps, without creating another node.

Validation: the complete module compiles server-side with scompile.py, both the sandbox
and the named library module; no errors or warnings. All binders use autoImplicit false;
no theorem other than the item's one sorry is introduced, and both definitions contain
actual map compositions. Final dry-run/delivery results are recorded below.

## Second reading by Q78

Independent second reading (maintainer reviewer; the earlier section was a second pass
by the first worker and is replaced). Node, source place (de Jong §§3.2, 3.6; the node's
seven proof steps), the module and the dependency declarations were read.

Hypotheses, against the Lean:

1. Field k: `(k : Type u) [Field k]`. Correct.
2. S normal integral projective finite type over k: `[IsIntegral S]`, `p : S ⟶ Spec k`
   with `[IsHProjective p] [LocallyOfFiniteType p] [QuasiCompact p]`, `hSnormal`
   (every stalk a domain and integrally closed = the node's convention). Correct.
3. K = k(S), F = k(X): `S.functionField`, `X.functionField`. The instance
   `[Algebra K F]` is pinned by `hKF`: f is dominant (the generic fibre is geometrically
   integral, hence nonempty, and f is closed with X irreducible), and morphisms
   `Spec F ⟶ S` through the generic point factor uniquely through the monomorphism
   `S.fromSpecFunctionField`. Not an extra assumption.
4. f H-projective, X integral of finite type over k: `[IsHProjective f]`,
   `[IsIntegral X]`, `LocallyOfFiniteType/QuasiCompact (f ≫ p)`. Correct. X normal:
   `hXnormal`. Correct.
5. Geometric fibres pure of dimension one: `hpure` over every algebraically closed
   `Ω : Type u` and every `Spec Ω ⟶ S` (also non-closed points), `IsPureDimension 1`
   (def-weil-pure-dimension). Correct.
6. C = X_K smooth, geometrically integral: instances on
   `pullback.snd f S.fromSpecFunctionField`. Mathlib's `GeometricallyIntegral` is
   `geometrically IsIntegral` (all field base changes integral). Correct.
7. M ⊂ C reduced finite étale closed: `i` closed immersion, `IsReduced M`, `IsFinite` and
   `Etale` of `i ≫ C → Spec K`. Correct.
8. Finite G acting compatibly, nonfaithfully, on k, X, S, f; M preserved: `σk, σX, σS`
   monoid homs (no faithfulness), `hk`, `hequiv`; `hMstable` on the image of M in X.
   σX g preserves the generic fibre (σS g fixes the generic point) and C → X is injective,
   so this is preservation of M ⊂ C (M reduced, so the closed set determines it).
   Conventions checked: `functionFieldAut E` is the pullback E^#
   (`SpecMap_functionFieldAut_hom_fromSpecFunctionField`), so
   `g ↦ functionFieldAut (σS g⁻¹)` is a left action (a monoid hom into E ≃+* E
   composition), matching `σk g⁻¹` in `hk`, `σE h⁻¹` / `σL h⁻¹` in the τS/τX equations,
   and HighGenusEquivariantCover. Hence the displayed fibre-product set is a subgroup and
   the iff-presentation is consistent.

Conclusions, against the Lean:

9. B = K^G: subfield characterized elementwise. Correct.
10. K'/K finite, Galois over B, containing K and all residue fields of M: E with
    `Algebra K E`, `Algebra B E`, `IsScalarTower B K E`, both `FiniteDimensional`,
    `IsGalois B E`; `∀ m, ∃ j : κ(m) →+* E` over K. Correct (j is a K-embedding).
11. G', N: injective pair `(β, σE)` whose image is exactly
    {(g, τ) | τ fixes B, τ|_K = g|_K}; β surjective; σE(ker β) = all ring automorphisms
    fixing K (= Aut_K(E), injectively by pair-injectivity); E^N = K elementwise. This is
    the node's G' up to the canonical isomorphism with its two projections. Correct.
12. F' = F ⊗_K E a field, finite separable over F: `IsField (F ⊗[K] E)` and `L` with
    `eL` pinned on pure tensors and both scalar towers; `FiniteDimensional F L`,
    `Algebra.IsSeparable F L`. Correct.
13. S' = Nor_E(S), X' = Nor_L(X) (`normalizationIn`, def-fin-normalization-extension):
    normal, integral, S'/k H-projective + finite type, X'/k finite type; S' → S finite
    surjective; r : X' → X ×_S S' pinned by its projections, finite surjective; q pinned
    by `q ≫ S'→S = X'→X ≫ f` and its generic compatibility; q H-projective, pure
    one-dimensional geometric fibres; generic fibre along the canonical `Spec E → S'`
    smooth and geometrically integral and `eC ≅ C ×_K E` pinned by both projections.
    Correct.
14. Action: σL on pure tensors `g(z) ⊗ σ(c)` with the inverse-pullback convention; τS, τX
    on the actual normalizations commuting with q, the maps to S, X, and the generic
    `Spec E`, `Spec L` maps; L^N = F elementwise. Correct.
15. Marking: n, E-sections `a j` of the generic fibre of q, pairwise disjoint, whose union
    is exactly the inverse image of M (transported by eC); G'-stable images in X'.
    n = 0 allowed (M = ∅). Correct.
16. Genus: for every Ω, s' : Spec Ω → S', hF pinned by projections; for each component
    Z' a component Z, h (pinned by `h ≫ ι_Z = ι_Z' ≫ hF`, ι a closed immersion) finite
    surjective, hν over the normalization maps, both normalizations smooth and proper over
    Ω, hν an Ω-map not factoring through an Ω-point (nonconstant), and
    `arithmeticGenus Z^ν ≤ arithmeticGenus Z'^ν` (def-pc-genus record) with the same Ω.
    The b-clause quantifies over `b : ℕ` and all geometric fibres on both sides. Correct.

Edge cases: M = ∅ (n = 0, residue clause vacuous); trivial and nonfaithful G; dim S = 0;
any characteristic; geometric points at non-closed points; inseparable component maps;
b = 0. Universes: schemes, fields and Ω in u; G : Type v, G' : Type (max u v). No extra
assumption (no flatness, faithfulness, closedness of geometric points).

Records and form: only the item node changed (`lean`, plus stmt_dep
def-weil-pbc-reduced-normalization, a landed definition node whose
`reducedNormalizationComponent` the statement uses; allowed by brief-stage2 §5).
`lean.statement` is verbatim the file signature; sole proof `by sorry`; the two helper
defs are the actual vanishing-ideal component inclusion and the composite normalized
structure map, with source and blueprint docstrings and listed in `lean.declarations`.
Module and theorem docstrings carry the source place, blueprint id and the seven proof
steps. Searches: an equivalent `componentι` exists only in the theorem-node module
NodalIdealScalarGluing (not citable); no duplicate statement in Mathlib, WeilConjectures
or Sheaf. Scheme.normalization (def-sc-normalization) and functionFieldAut (upstream
StalkAut) are reached through the transitive closure/upstream; advisory only.

No mismatch found; no Lean or record change.
