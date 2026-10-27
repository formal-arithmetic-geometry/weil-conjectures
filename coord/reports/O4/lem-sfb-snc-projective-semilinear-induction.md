## Worker report

The module `Sheaf.AlgebraicGeometry.SNCProjectiveSemilinearInduction` states
`AlgebraicGeometry.snc_projective_semilinear_induction`. Its only theorem proof is
`sorry`; no definitions or helper theorems are introduced. The node is unchanged
except for its `lean` field. There is no statement correction or disputed claim.

Source checked: ILO, Travaux de Gabber, Expose X, printed p.149 (relative SNC
intersection definition), pp.150--151, Step 2 and diagram (2.b). Read directly
using pdftotext on PDF pages 155--157. The node's eight-step proof, including
its affine radical calculation, coordinate-block embedding, absolute projectivity
and closed-graph verification, is reproduced in the theorem docstring.

### Hypotheses and the constructed objects

* `e : Type u` with `[Field e]` renders the field e.
* `I : Type w` with `[Finite I] [Nonempty I]` renders the nonempty finite family;
  the separate index universe is allowed because every finite type is small.
* `B : I → Scheme.{u}`, `b i : B i ⟶ Spec (.of e)`, `[IsIntegral (B i)]`,
  and `[IsProper (b i)]` give the integral proper e-schemes. The finite-type
  clause is included in properness: its parent gives `LocallyOfFiniteType`,
  and `UniversallyClosed` gives `QuasiCompact`. Explicit duplicate instances
  triggered the overlapping-instances warning and were removed; no mathematical
  hypothesis was dropped. The total B is Mathlib's chosen coproduct `∐ B`.
* `Ci i : (B i).IdealSheafData` and `hCi` give the effective Cartier ideals.
  `C : (∐ B).IdealSheafData` with `hC` states exactly their disjoint union:
  pullback to each coproduct summand is `Ci i`. These restrictions determine
  C uniquely, since the summands form a disjoint open cover.
* `F : I → Type u`, its field and e-algebra instances, and
  `[∀ i, Module.Finite e (F i)]` render the finite extensions F_i/e.
* `J : I → Type v`, its group and finiteness instances, and
  `rho i : J i →* (F i ≃ₐ[e] F i)` give the finite groups acting by
  e-automorphisms. No faithfulness is assumed.
* `S`, `p`, `[IsIntegral (S i)]`, `[Smooth (p i)]`, and
  `[IsHProjective (p i)]` render integral smooth projective S_i/F_i using
  precisely the finite-projective-space convention of the dependency node.
* `a i : J i →* Aut (S i)` gives the left scheme action; `ha` is its
  semilinearity. The inverse in `Spec.map (rho i j⁻¹)` is necessary because
  Spec is contravariant. `Aut` multiplication uses function-composition order.
* `vS i : S i ⟶ B i`, its `Surjective` instance, `hbase`, and `hinvariant`
  render the invariant surjective e-morphism. `hgeneric` says it maps the
  generic point of S_i to that of B_i; integral schemes have a unique such
  point. `hfinite` says the actual induced residue-field ring homomorphism
  at that point is finite, without choosing an unrelated algebra structure.
* `hD` is the existing SNC predicate on `((Ci i).comap (vS i)).radical`.
  `comap` is the inverse-image ideal, `radical` gives its reduced structure.
* `K`, `[Field K] [Algebra e K] [Module.Finite e K] [Normal e K]` and
  `emb i : F i →ₐ[e] K` give the common finite normal extension and embeddings.
  `Normal` is the minimal-polynomial splitting condition, equivalent to the
  stated irreducible-polynomial condition for an algebraic/finite extension.
  It includes no separability requirement.
* `G : Type t`, `[Group G] [Finite G]`, and `pi : G →* (K ≃ₐ[e] K)` give
  the finite group and its e-linear scalar action, which need not be faithful
  or surject onto all automorphisms. `Gamma`, `r`, `hr`, and `hcompatible`
  render the subgroups, surjections to J_i, and equality of actions on F_i.
* The exact `pullback (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom))`
  is W_i. `d` with `hdS` and `hdK` specifies its diagonal action by its two
  projections. Pullback uniqueness determines this action; it is not arbitrary.
* `Y i`, `q i`, `tY i g`, `s`, `hs`, and `hcoproduct` specify the actual
  contracted product as a coset coproduct of W_i. `hs` means left-coset
  representatives. `hcoproduct` is a proof of the universal property
  `Nonempty (IsColimit (Cofan.mk ...))`, not a Nonempty choice of scheme data.
  Every realization of this coproduct is uniquely isomorphic to the chosen
  coproduct preserving the indicated injections. No extra quotient or
  smoothness/projectivity assumption is put on it.
* `hrelation` is exactly `(g gamma,w) ~ (g,gamma w)` as equality of maps.
  `hscalar` gives the scalar twist of the copy g by `Spec(pi(g)⁻¹)`.
  `aY` and `hleft` specify left multiplication; the coproduct determines
  this action. These equations are the construction specifications, following
  the already landed CommonFieldSemilinearInduction interface, rather than
  added restrictions on the original input data.
* `fY` and `hmap` specify the unique maps `[g,w] ↦ v_i(pr_1 w)` by all
  coproduct injections. The total Y is the chosen coproduct `∐ Y`; its
  K-structure is the actual map `Sigma.desc q`. The total h is the actual
  map `Sigma.desc (fun i ↦ fY i ≫ Sigma.ι B i)`. Invariance and compatibility
  with the e-structures follow from the displayed translate equations and
  the universal property. No unconstrained map replaces the canonical h.

### Every conclusion

1. Smoothness over K is `Smooth (Sigma.desc q)`.
2. Geometric reducedness over K is `GeometricallyReduced (Sigma.desc q)`.
3. Reducedness is `IsReduced (∐ Y)`.
4. Projectivity over K in finite projective space is `IsHProjective (Sigma.desc q)`.
5. Projectivity over e in finite projective space is `IsHProjective
   (Sigma.desc q ≫ Spec.map (CommRingCat.ofHom (algebraMap e K)))`.
6. The finite-projective-space conclusion for h is `IsHProjective` on the
   above `Sigma.desc` map; the projective-bundle conclusion is the distinct
   existing predicate `IsProjectiveBundle` on precisely the same map.
7. Surjectivity is `Surjective` on that map.
8. The final conjunct applies `IsSmoothStrictNormalCrossingsDivisor` to
   `Sigma.desc q` and `(C.comap h).radical`. Its definition includes the
   effective Cartier condition, reduced closed subscheme, finitely many
   distinct integral components, their union, and smooth scheme-theoretic
   intersections of pure codimension equal to the number chosen. Its
   `Finset` quantifier includes the empty set (intersection the ambient Y),
   and empty intersections impose no minimal-prime height condition.

### Dependency declarations used

Every statement-dependency record and its declaration signature/docstring was read.
The dependency interfaces are usable without repairs:

* def-kun-projective: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`.
* def-nagata-effective-cartier-ideal:
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`,
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`.
* def-pc-fibre-product: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
* def-pc-field-extension: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
* def-pc-field-tower: `Sheaf.FieldTheory.FieldTower`, whose documented finite
  extension interface is Mathlib's `Module.Finite` (the numeric `degree` is not needed).
* def-pc-geometrically-irreducible: `Mathlib.AlgebraicGeometry.Geometrically.Integral`,
  importing `AlgebraicGeometry.GeometricallyReduced` from `Geometrically.Reduced`.
* def-pc-integral-scheme and def-pc-reduced-scheme:
  `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`,
  `AlgebraicGeometry.IsReduced`.
* def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.
* def-sc-generic-point: `Mathlib.Topology.Sober`, `genericPoint`,
  `genericPoint_spec`, `IsGenericPoint`.
* def-trf-projective-bundle-morphism:
  `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`,
  `AlgebraicGeometry.IsProjectiveBundle`.
* def-trf-smooth-strict-normal-crossings-divisor:
  `Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor`,
  `AlgebraicGeometry.Scheme.IdealSheafData.IsSmoothStrictNormalCrossingsDivisor`.
* def-weil-field: `Mathlib.Algebra.Field.Defs`, `Field` (Mathlib match).
* def-weil-finite-type-morphism:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and `Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact`; inferred here from `IsProper`.
* def-weil-proper-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
* def-weil-residue-field: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and `Scheme.Hom.residueFieldMap`.
* def-weil-surjective-morphism:
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `AlgebraicGeometry.Surjective`.

Public imports expose the statement notions; all already recorded proof-dependency
modules are plain imports, or are included already by a public dependency import.
`lem-sfb-relative-snc-field-extension` has no recorded declaration and hence no
module to import; its precise role remains in the docstring and DAG proof. It
is a proof prerequisite only, not a missing statement notion for this delivery.

### Edge cases checked

* The empty divisor is the unit ideal; its radical stays the unit ideal. The
  SNC definition allows zero components. No boundary-nonempty hypothesis occurs.
* For r=0 the SNC definition uses the empty finite set, so `s.sup C` is the
  zero ideal and its closed subscheme is the whole ambient scheme; the smooth
  and codimension-zero clause is retained.
* Unequal dimensions of different B_i and S_i are unrestricted; there is no
  common-dimension parameter. Empty intersections of strata are allowed.
* Purely inseparable finite K/e and F_i/e are included: no IsSeparable,
  IsGalois or perfect-field instance is introduced. A normal purely inseparable
  extension with trivial automorphism action is allowed.
* I is nonempty exactly as specified. Trivial groups, Gamma=G, and Gamma=1
  are included. Scalar actions can have kernels. Finite index/group types
  can live in independent universes and have the required Small instances.
* Integral sources and bases are nonempty, exactly as in the node, without
  imposing geometric integrality on S_i. Base change of integral S_i may
  split into multiple components, as the SNC predicate permits.

### Searches

No exact existing statement was found. msearch.py was invoked with the assigned
O4/item identifiers for each search, with these queries and results:

* `loogle`: `AlgebraicGeometry.IsHProjective, AlgebraicGeometry.Smooth`. Result: 0 hits; loogle: unknown identifier 'AlgebraicGeometry.IsHProjective'; . No exact statement.
* `leanfinder`: `A finite disjoint union of scalar twists of smooth projective schemes with a strict normal crossings divisor is smooth projective with strict normal crossings`. Result: 8 hits; AlgebraicGeometry.instIsMultiplicativeSchemeIsSmoothOfRelativeDimensionOfNatNat, AlgebraicGeometry.IsSmoothOfRelativeDimension, AlgebraicGeometry.instIsSmoothOfRelativeDimensionOfNatNatCompScheme, AlgebraicGeometry.isSmoothOfRelativeDimension_comp, AlgebraicGeometry.Scheme.Hom.normalizationCoprodIso, AlgebraicGeometry.IsSmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension, AlgebraicGeometry.Scheme.Hom.inr_normalizationCoprodIso_hom_fromNormalization, AlgebraicGeometry.Scheme.Hom.inr_normalizationCoprodIso_hom_fromNormalization_assoc. No exact statement.
* `grep`: `semilinear|normal.?crossing|contracted.?product` in `AlgebraicGeometry`. Result: 4 hits; Mathlib/AlgebraicGeometry/StructureSheaf.lean, Mathlib/AlgebraicGeometry/StructureSheaf.lean, Mathlib/AlgebraicGeometry/StructureSheaf.lean, Mathlib/AlgebraicGeometry/StructureSheaf.lean. No exact statement.
* `leansearch`: `Finite semilinear induction preserves smooth projective schemes and strict normal crossings divisors`. Result: 8 hits; AlgebraicGeometry.Scheme, AlgebraicGeometry.IsSmooth.casesOn, AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme, AlgebraicGeometry.instLocallyOfFinitePresentationOfIsSmooth, AlgebraicGeometry.IsSmooth, AlgebraicGeometry.IsSmooth.recOn, Algebra.FormallySmooth.instForallOfFinite, AlgebraicGeometry.instIsProperOfIsFinite. No exact statement.

Direct rg searches of `lean/WeilConjectures` and `lean/Sheaf` for
`semilinear|Semilinear|contracted|Contracted|induced.*[Ss]cheme|Induced.*[Ss]cheme`
found module/linear semilinearity and other alteration results, but no exact
smooth/SNC/absolute-and-relative-projectivity conclusion. Searching the item id
in WeilConjectures returned no hit. Searching `dag/lean_names_upstream.json`
for the proposed declaration found no clash. DAG search found
`lem-sfb-common-field-semilinear-induction` and `lem-sfb-semilinear-coset-scheme`;
they concern construction and orbit/generic-point properties, not the present
geometric conclusions. Read the former's landed module and used the same
universal-property/translate-equation presentation; no existing notion is copied.

### Validation

Compiled the only delivered module with the prescribed server scompile.py.
After fixing a line-break parsing issue and removing redundant finite-type
instance binders, both sandbox and named-library compilations succeeded with
no warnings or errors. All universes and variables are explicitly bound;
autoImplicit is false. Delivery dry run and push are performed after this report.

## Second reading by O4

Independent clause-by-clause reading (maintainer review service, 2026-10-24), replacing the
worker's own final self-check, which was not an independent reading. Delivery head
760000174971; the Lean module, the node record and the worker report above are unchanged.

Source: ILO, Travaux de Gabber, Expose X, 2.1 (relative SNC, p.149) and 2.3 Step 2,
contracted product and diagram (2.b), pp.150--151.

Node clauses and their Lean:

* e field: `e : Type u`, `[Field e]`. Correct.
* I nonempty finite: `[Finite I] [Nonempty I]`, own universe w; `∐ B` exists by
  `hasColimitsOfShape_discrete` for finite index types. Correct.
* B_i integral, proper, finite type over e: `IsIntegral (B i)`, `IsProper (b i)`; Mathlib
  `IsProper` extends `LocallyOfFiniteType`, and universal closedness gives quasi-compactness.
  Correct, not stronger.
* C_i effective Cartier, C their disjoint union: `hCi : (Ci i).IsInvertible`,
  `hC : C.comap (Sigma.ι B i) = Ci i`; restrictions to the disjoint open summands determine C.
  Correct.
* F_i/e finite: `Algebra e (F i)`, `Module.Finite e (F i)`. Correct.
* J_i finite acting by e-automorphisms: `rho i : J i →* (F i ≃ₐ[e] F i)`, no faithfulness. Correct.
* S_i integral smooth projective over F_i: `IsIntegral`, `Smooth (p i)`, `IsHProjective (p i)`
  (upstream class: closed immersion into `ℙ(n; S)` with `Finite n`). Correct.
* Semilinear action: `a i : J i →* Aut (S i)` with `ha`. Mathlib `Aut` multiplication is
  `x * y = y ≪≫ x`, so `a` is a left action; on rings `(a j)^♯ ∘ p^♯ = p^♯ ∘ rho(j⁻¹)`, and
  `j ↦ rho(j⁻¹)` is the required anti-homomorphism. Checked consistent.
* v_i invariant surjective e-morphism, generic point to generic point, finite residue
  extension: `vS`, `Surjective`, `hbase`, `hinvariant`, `hgeneric`, `hfinite` on
  `residueFieldMap` at the generic point. Correct.
* D_i = (v_i^{-1}C_i)_red relative SNC over F_i: Mathlib `IdealSheafData.comap I f` is
  `(pullback.fst f I.subschemeι).ker`, the ideal of the scheme-theoretic inverse image; `radical`
  is the reduced structure; `IsSmoothStrictNormalCrossingsDivisor (p i)` is the recorded
  def-trf node (invertible, reduced, finitely many integral pairwise noncontained components,
  every `s : Finset`, including `s = ∅`, smooth of pure codimension `card s`). Correct.
* K/e finite normal: `Module.Finite e K`, `Normal e K` (equivalent to the node's irreducible
  polynomial formulation for algebraic extensions), no separability. Embeddings `emb`. Correct.
* G finite acting by e-automorphisms `pi`; Γ_i, surjections `r`, `hr`, agreement `hcompatible`.
  Correct.
* W_i with diagonal Γ_i-action: `pullback (p i) (Spec.map (emb i))`, `d` with `hdS`, `hdK`.
  I checked that the two required composites agree by `ha`, `hcompatible`, so `d` exists and is
  unique by the pullback property, and that `hdS` is compatible with `d`, `a`, `r` being
  homomorphisms. Not an arbitrary choice.
* Y_i = G ×^{Γ_i} W_i: `tY`, coset representatives `s`, `hs`, `hcoproduct` (universal property,
  a Prop), `hrelation` = (gγ,w) ~ (g,γw) in diagrammatic order, `hscalar` (copy g twisted by
  pi(g)), `hleft`, `hmap` = [g,w] ↦ v_i(pr_1 w). Checked: `hscalar` and `hmap` are compatible
  with `hrelation` (using hdK, hdS, hinvariant), and `hleft` is compatible with `aY` being a
  homomorphism; hence all data are determined by and realizable from the coset coproduct. Same
  interface as the landed `common_field_semilinear_induction`, whose conclusion supplies
  exactly these data; the item composes with it.
* Conclusions: `Smooth`, `GeometricallyReduced` (recorded in def-pc-geometrically-irreducible),
  `IsReduced (∐ Y)`, `IsHProjective` over K and over e (`Sigma.desc q ≫ Spec.map (algebraMap e K)`),
  `IsHProjective` and `IsProjectiveBundle` for h = `Sigma.desc (fY i ≫ Sigma.ι B i)`,
  `Surjective h`, and SNC of `(C.comap h).radical` over K. All nine clauses present, none weaker
  or stronger.

Edge cases: empty divisor (C = ⊤, comap ⊤ = ⊤, n = 0 components); r = 0 (empty Finset); purely
inseparable K/F_i ((D_a)_K stays smooth hence reduced, and the flat base change of the
intersection of component ideals is the intersection, so the radical is (D_i)_K; components may
split, which the predicate allows); trivial groups, Γ_i = G or 1, nonfaithful pi; unequal
dimensions of B_i. No extra hypothesis excludes any of them.

Records: the item node differs from live only by its `lean` field; `lean.statement` equals the
file signature verbatim (checked programmatically). Proof-dependency imports exist on live.
Gates: no definitions, theorem proof `sorry` only, module and theorem docstrings carry the
source place and `(blueprint: lem-sfb-snc-projective-semilinear-induction)`, the theorem
docstring gives the eight proof steps; no pro-etale substitute.

Searches: Mathlib AlgebraicGeometry and project lean/Sheaf, lean/WeilConjectures for
semilinear/contracted/normal crossing induction statements; only the construction lemma
common_field_semilinear_induction (different conclusions). No duplicate.

Findings: none in the mathematics or records. Only change: this section (report form).
