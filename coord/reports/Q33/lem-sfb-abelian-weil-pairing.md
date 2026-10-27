## Worker report

The repaired delivery states `AlgebraicGeometry.IsAbelianVariety.exists_functorial_weilPairing`
in `Sheaf.AlgebraicGeometry.AbelianVariety.WeilPairing`. Its only theorem proof is
`sorry`. `RationalDualityData` supplies a transparent package of the already supplied
variety and dual, and the pullback classifier. Integral and rational homomorphisms are
imported from the landed `RationalHom` module. No dual, pairing, or morphism is chosen from an
uncharacterized existence statement. The item statement and proof are unchanged.

Hypothesis and clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
  All varieties and duals have this same base and universe. Arbitrary `A,B,C`
  in the node are represented by `A B C : AbelianVarietyWithDual k`; its fields
  are precisely the variety, its `GrpObj`, `IsAbelianVariety`, and the supplied
  `AbelianDualPoincareDatum`. This is not a choice of a preferred dual and imposes
  no extra property on the abelian varieties or supplied duals. Universally
  quantifying these packages supplies a simultaneous family of pairings, as
  needed by functoriality for every homomorphism.
- Group-scheme homomorphisms are the existing Mathlib homs
  `Grp.mk A ⟶ Grp.mk B`. `abelianHom` changes these to additive notation.
  The imported `RationalHom` definition uses pointwise multiplication into the
  commutative group object,
  hence exactly addition of abelian-variety homomorphisms. The underlying
  scheme morphism is `f.toMul.hom.hom` and already has `IsMonHom`.
- The existential `d A B : ... →+ ...` states additivity of pullback duality.
  The first conjunct characterizes its underlying map by precisely the Poincare
  pullback isomorphism in the recorded polarization-calculus interface:
  `A.dualHomClassifies B f g ↔ g = d A B f`. The next two conjuncts state
  reversed composition and the dual of the identity. Thus an arbitrary map
  cannot satisfy the interface in place of pullback on duals.
- `abelianRationalHom A B` is literally `ℚ ⊗[ℤ] abelianHom A B`.
  The `ℚ`-linear maps `dQ` extend `d` by
  `dQ A B (q ⊗ₜ f) = q ⊗ₜ d A B f`. The bilinear `cQ` and `cD` are
  normalized on **every** pure tensor by actual composition of bundled group
  homomorphisms. This determines the canonical rational compositions by the
  tensor universal property. Their existence asserts only that this indicated
  bilinear extension exists; it does not replace composition by an arbitrary
  map. The subsequent conjuncts give contravariance on arbitrary rational
  homomorphisms and the rational identity formula. Rational additivity is
  already part of the `LinearMap` type.
- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`, and `hℓ : ℓ ≠ ringChar k`
  is exactly the prime-to-characteristic hypothesis, including characteristic
  zero. There is no condition on an isogeny's degree.
- The line is `AddCommGroup.rationalTateModule ℓ (Additive kˣ)`, the existing
  definition `ℚ_[ℓ] ⊗[ℤ_[ℓ]] AddCommGroup.tateModule ℓ (Additive kˣ)`.
  The latter's coordinate conditions say `z_n^(ℓ^n)=1` and
  `z_(n+1)^ℓ=z_n`. Thus this is precisely the root inverse limit in the node,
  rationalized using tensor symmetry relative to the node's notation. The
  extra `n=0` coordinate is forced to one. No new Tate-line definition is
  introduced. `Nonempty (... ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ])` states exactly dimension one.
- The family `e A` is a curried `ℚ_[ℓ]`-bilinear map on the **recorded**
  `IsAbelianVariety.rationalTateModule` of the variety and its specified dual.
  `Function.Bijective (e A)` and `Function.Bijective (e A).flip` are exactly
  the two isomorphisms to the line-valued linear duals, not only one-sided
  radical vanishing or a scalar-valued replacement pairing.
- `v` and `vD` are additive maps on rational homomorphism spaces with values
  in `ℚ_[ℓ]`-linear maps between the actual rational Tate modules. Their
  pure-tensor normalization is `(q : ℚ_[ℓ]) • rationalTateModuleMap f`.
  This uniquely determines their rational actions. Additivity plus these
  formulas is equivalent to rational linearity: expand a tensor into a finite
  sum of pure tensors and use the rational cast identities. Using `→+` here
  avoids adding a second rational scalar instance on the upstream Tate types.
  The existing `rationalTateModuleMap` is the scalar extension of the actual
  componentwise `tateModuleMap`, not an unspecified linear representation.
- The next conjunct is the exact rational adjoint identity
  `e B (v A B f x) y = e A x (vD A B (dQ A B f) y)` for every rational `f`
  and both arbitrary vectors.
- The last conjunct quantifies `L : A.variety.left.Modules`, assumes
  `L.IsInvertible`, and uses **the recorded** `ClassifiesAbelianDifference`
  to identify `φ` with `φ_L`. It obtains the homomorphism proof `hφ` rather
  than adding that as a new hypothesis. `∀ x, e A x (V(φ) x) = 0` states
  alternation. The explicit `@rationalTateModuleMap ... hφ` only passes that
  proof to the existing componentwise map; it introduces no new map.
  Under `IsIsogeny φ` the two final implications assert that both radicals
  of `(x,y) ↦ e A x (V(φ)y)` vanish, exactly nondegeneracy.

Dependency declarations read and used:

- `Field` (`Mathlib.Algebra.Field.Defs`) and `IsAlgClosed`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`); no algebraic closure is chosen
  anew. The upstream Tate module already uses `Scheme.specAlgebraicClosure k`.
- `IsAbelianVariety`, `IsAbelianVariety.dim`
  (`WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`), and `GrpObj`,
  `Grp.mk`, `Grp.homMk`, and bundled group homs in
  `Mathlib.CategoryTheory.Monoidal.Grp` / `.Cartesian.Grp`.
- `IsAbelianVariety.exists_dual_polarization_calculus`
  (`Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus`), and its
  actual datum `AbelianDualPoincareDatum`, `ClassifiesAbelianDifference`
  (`Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum`). The full
  universal family and supplied identity-axis rigidification are reused.
  The new pullback-characterization predicate follows the exact isomorphism
  of universal families used by this recorded dependency. Its literal
  `Scheme.Modules.pullback` agrees with that interface; no second module
  inverse-image functor is constructed.
- `IsAbelianVariety.tateModule`, `.rationalTateModule`, `.tateModuleMap`,
  `.rationalTateModuleMap`, and `.tateModuleEquivTorsionPoints`
  (`WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule`), read in
  full with their coordinate formulas and signatures. The closed upstream
  audit on `sk-def-av-tate` is used, not restated.
- `TensorProduct` / tensor universal property
  (`Mathlib.LinearAlgebra.TensorProduct.Defs` / `.Basic`), `Padic`,
  `PadicInt`, and the residue maps (`Mathlib.NumberTheory.Padics.*`).
- `Scheme.Modules.IsInvertible`
  (`WeilConjectures.AlgebraicGeometry.Modules.Invertible`) and `IsIsogeny`
  (`WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`). The latter is
  surjectivity plus finite scheme-theoretic kernel, not a point-kernel or
  prime-to-ℓ restriction.

The file imports the recorded modules of all stated proof dependencies, with
plain `import`. The two currently unstated proof dependencies
`lem-sfb-finite-torsion-weil-pairing` and `lem-sfb-simple-isogeny-decomposition`
have no module to import; they are named in the seven-step proof docstring.
They are not needed to type the statement, and no replacement theorem is added.
The public statement imports are available through the supplied data, Tate,
polarization-calculus and group-scheme modules.

Edge cases checked before finalizing:

- The zero-dimensional/trivial abelian variety is allowed. Its zero Tate
  module maps bijectively to the zero line-valued dual; no positive dimension
  is assumed. The cyclotomic line is still one-dimensional.
- `ℓ=2` is included. Alternation is expressed as a zero diagonal over
  characteristic-zero `ℚ_[2]`, not inferred by excluding two.
- `ringChar k=0` is included. The prime hypothesis excludes zero and one;
  no artificial positive-characteristic binder occurs.
- Trivial/nonample invertible sheaves are included: alternation always,
  nondegeneracy only under the stated isogeny hypothesis.
- Isogenies of degree divisible by `ℓ` are included; rational, rather than
  integral, nondegeneracy is stated.
- Zero rational homomorphisms, identities and arbitrary denominators are
  included by the tensor domains and normalizations for every `q : ℚ`.
- Universes are explicitly bound; the new package uses the same universe as
  the original scheme/field/Tate interfaces. Both auto-implicit options are
  disabled in both delivered modules.

Searches performed (the sandbox `searches.jsonl` contains the exact service outputs):

- `msearch.py leanfinder`: “The Weil pairing between rational Tate modules
  of dual abelian varieties is perfect functorial and alternating for a
  polarization”: eight root-system pairing results, no geometric Weil pairing.
- `msearch.py loogle`: `AddCommGroup.rationalTateModule, AddCommGroup.tateModule`:
  zero hits, service does not index this upstream declaration. Its actual
  definition was found and read in the project.
- `msearch.py grep`: `WeilPairing|weilPairing|rationalHom|TateTwist`: zero hits.
- `msearch.py leansearch`: “Tate twist of field units is rational Tate module
  of roots of unity”: eight cyclotomic-character/number-field results, no
  geometric pairing. The exact cyclotomic Tate module is already documented
  in `WeilConjectures.NumberTheory.TateModule`; it is reused literally.
- `msearch.py leansearch`: “Abelian variety with a chosen dual Poincare line
  bundle rational homomorphisms”: eight root-pairing and additive-character
  results, no match for the supplied-data/rational-hom package.
- `msearch.py leanfinder`: “Bundled abelian variety with specified dual
  Poincare datum and rational homomorphism tensor space”: root data,
  Weierstrass curves and `Ab`; no matching package.
- `rg` of Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no declaration with any delivered name.
  Existing `IsWeilPairing` declarations concern Frobenius on derived étale
  sheaves, not the Weil pairing of abelian varieties. The item-id search
  finds no existing result. The datum and Tate declarations above are reused.
- DAG grep for a specified dual package/rational hom space finds the existing
  Poincare datum, which is imported rather than duplicated.
  `tools/blueprint_refs.py search 'dual abelian'`: zero matches.

Source checked: the local Milne PDF, extracted with `pdftotext -layout`,
I §13 printed pp.57–58, including the root-limit formula and Proposition
13.2(a),(d). The supplied proof's seven steps are preserved in the theorem
proof docstring, including the primitive-root, finite-perfectness and
multiple-inverse arguments. No statement fault or `STATEMENT-DISPUTED` claim.

## New nodes

`def-sfb-abelian-rational-duality-data` packages the existing `GrpObj` abelian
variety with its supplied `AbelianDualPoincareDatum`, and defines only the
Poincare-family pullback classifier. It public-imports
`Sheaf.AlgebraicGeometry.AbelianVariety.RationalHom` and uses its `abelianHom`.
It owns exactly `AbelianVarietyWithDual` and `AbelianVarietyWithDual.dualHomClassifies`.
Source: Milne AV I §§8–9, pp.36–41. Neither declaration contains a theorem/sorry.
The retained historical searches predate the concurrent landing of
`def-sfb-abelian-rational-hom`. The repaired module imports that node
and contains no hom-space definition. The specified-dual package and
its pullback classifier remain new. Its blueprint ancestor is null because
that is the item's own ancestor and the ancestor tool explicitly reports
`blueprint.from.node = None`; its `via` starts with this item and retains
the item's chain. No upstream node is edited to repair that historical chain.

## Second reading by Q33

In-thread rereading, not an independent-agent endorsement: the dispatcher
explicitly instructed this worker not to start other agents; the maintainer
performs the independent review after delivery. I reopened the node and both
modules and checked every item above against their signatures. In particular,
I checked the order of the two rational dual hom spaces in `cD`, the composition
order `f ≫ g` versus `(d g) ≫ (d f)`, both bijections in perfectness, the
same existential `dQ` in the rational adjoint identity, and that `φ_L` is tied
to the recorded normalized-difference family. The scalar-interface compile
failure was repaired by using normalized additive rational actions, which are
equivalently rational-linear by the tensor relations. The main statement
contains no hidden `let`, private notation, arbitrary Tate representation,
extra positivity assumption, or restriction on isogeny degree. All definitions
have actual data. Only the item's theorem is postponed.


## Returned-delivery repair

The maintainer returned immutable head `87cab2c205a9` for H4/H12 and H9:
`RationalDualityData` collided with the subsequently landed owner
`def-sfb-abelian-rational-hom` (`N9`, `RationalHom`, landed 2026-10-24 04:12 UTC).
The current published node/module were read in full. Compared with the retained
item, the current base has no change to its mathematical statement/proof; the
wrapper will construct this repaired delivery on the current published base.

1. `RationalDualityData` now public-imports `RationalHom`. Both local hom-space
   declarations are removed, rather than renamed. It declares only the package
   `AbelianVarietyWithDual` and `dualHomClassifies` (plus generated structure
   projections). Its classifier uses the owner's `abelianHom`.
2. The new node's statement and declaration list are narrowed to those two
   notions. Its statement dependencies cite `def-sfb-abelian-rational-hom`.
   Its historical search results are retained with a fresh landed-owner search
   and explicit reuse verdict; they no longer justify a duplicate hom notion.
3. The theorem uses `abelianHom` everywhere instead of the removed synonym.
   `abelianRationalHom` resolves to the existing N9 declaration. Its mathematical
   clauses, pure-tensor normalizations, proof docstring and sole `sorry` remain
   those accepted by the independent review. `lean.statement` is regenerated
   verbatim from the revised signature.
4. The advisory owning-node dependencies are now explicit on the item:
   `def-sfb-abelian-rational-hom`, `def-sfb-abelian-dual-poincare-datum`, and
   `sk-d-ab-tate`. The last has a closed upstream audit naming
   `AddCommGroup.rationalTateModule` in `WeilConjectures.GroupTheory.TateModule`;
   its full defining source was already read. Both datum and Tate modules are
   explicit public imports. The original `lem-sfb-abelian-polarization-calculus`
   dependency/import stays: the statement assumes its supplied duals and pullback
   homomorphisms, with the actual definitional data supplied by its owning node.
5. Consumer validation: compile a module-mode joint-import probe containing the
   repaired `WeilPairing` and the current `PolarizationCalculusOverField`.
   These are the two interfaces needed by
   `lem-sfb-ample-polarization-positive-spectrum`; this reproduces the exact
   import combination reported to collide. The scratch probe is excluded from
   delivery. Compile and dry-run outcomes are recorded below after execution.


Repair validation: `scompile.py` successfully compiled both delivered modules
separately (RationalDualityData 5.2 s; WeilPairing 3.5 s), with no diagnostics.
A second authorized compile included `scratch/CompatibilityProbe.lean` in module
mode with public imports of the repaired `WeilPairing` and landed
`PolarizationCalculusOverField`; both sandbox and library checks succeeded
(the latter 2.1 s). Its `#check`s resolve the single imported `abelianHom` and
`abelianRationalHom`, the classifier, and both consumer-facing theorem types.
No `environment already contains` errors remain. The probe is outside `lean/`
and is not a delivery file. The original mathematical statement remains
unchanged; only its declaration ownership/dependencies and exact Lean spelling
were repaired as requested.
