## Worker report

The module `Sheaf.RingTheory.DvrAlgebraicNormalizationStructure` states
`IsDiscreteValuationRing.algebraic_normalization_structure`, with `sorry` as its entire
proof. No theorem is proved and no construction is chosen from an existence theorem.
The item's natural-language statement and accepted proof are unchanged.

Source read: `literature/stacks-project/more-algebra.tex`, Tag 09EM
(`remark-construction`, especially (1)–(3)), and Tag 09IH
(`lemma-big-extension-is-ok`, statement and full proof). The current blueprint is
`literature/blueprint/latest`; the item's recorded ancestry is historical supporting
algebra for its Epp input, not a current blueprint unit statement. No unit is changed.

Hypotheses and objects, in statement order:

- `A`, `B` have `CommRing`, `IsDomain` and `IsDiscreteValuationRing` instances.
  `Algebra A B` is the given ring map, `hinj` its injectivity and
  `IsLocalHom (algebraMap A B)` its locality. For local rings the latter says precisely
  that the maximal ideal pulls back to the maximal ideal (units are reflected).
- `K` and `L` are fields with `IsFractionRing A K` and `IsFractionRing B L`.
  `Algebra K L` and the two scalar towers express compatibility of the fraction-field
  inclusion with the original map. Each of A, B, K, L and P has its own universe.
- `P` is a field with `Algebra K P`, `Algebra.IsAlgebraic K P`, and the induced
  compatible A-algebra structure (`IsScalarTower A K P`). No separability, perfection,
  characteristic, completeness, henselianity or Nagata hypothesis occurs.
- The lower closure is Mathlib `integralClosure A P`. The upper closure is the existing
  `eppUpperClosure B K L P`, literally the integral closure of B in
  `eppReducedTensor K L P`. The latter is the quotient of `L ⊗[K] P` by its nilradical,
  so nilpotents of every order are killed. Contraction uses the existing
  `eppNormalizationMap A B K L P`, whose value is the class of `1 ⊗ p`.
- `hcase` is the exact disjunction: `Module.Finite K P`, or the presentation
  `∃ U, ∃ CommRing U, ∃ Algebra A U, ∃ p, ∃ p.IsPrime, ...` with
  `RingHom.FiniteType (algebraMap A U)` and
  `Nonempty (B ≃ₐ[A] Localization.AtPrime p)`, together with Noetherianity of the
  lower closure. The universe `max u v` for U suffices: any finite polynomial
  presentation can be transported to that universe. The presentation is retained
  verbatim rather than replacing essential finite type by finite type of B.

Conclusion clauses, in conjunction order:

1. `∃ t > 0, ∃ F : Fin t → Type (max x y), ...` supplies a nonempty finite family
   of fields, L-algebra structures, `Algebra.IsAlgebraic L (F i)`, and an L-algebra
   equivalence `eppReducedTensor K L P ≃ₐ[L] ∀ i, F i`. It asserts algebraicity,
   without inserting separability or finiteness in case (b).
2. `IsNoetherianRing` of both lower and upper closures gives their Noetherianity.
   `Finite (MaximalSpectrum ...)` of each is exactly finitely many maximal ideals.
3. `IsDomain (integralClosure A P)` states the lower-domain clause explicitly.
   A finite family D, commutative-ring and domain instances, `IsIntegrallyClosed`,
   and a ring equivalence from the upper closure to `∀ i, D i` give its product
   decomposition. Each factor has every nonzero prime maximal AND an existential
   nonzero prime. Thus dimension is exactly one, including the non-field requirement.
   `IsIntegrallyClosed` means integral closedness in Mathlib's `FractionRing`.
   The upper ring is nontrivial as a subring of the nonzero reduced tensor, so any
   such product is automatically nonempty even though its second index t is not
   separately constrained.
4. For every ideal q with `[q.IsMaximal]`, `q.comap (eppNormalizationMap ...)` is
   maximal. Its primality is inferred from comap of a prime, without assuming the
   maximality conclusion in a binder. The lower localization has
   `IsDiscreteValuationRing`. For the upper localization the conjunction explicitly
   supplies its domain instance and then its `IsDiscreteValuationRing` instance;
   the domain property is not assumed beforehand.
5. For every such q, the exact case-(b) hypothesis implies
   `IntermediateField.FG ⊤` for the algebra structure induced by
   `Ideal.ResidueField.map` along the canonical contraction. This is field generation,
   allowing transcendence, and not finite generation as a ring algebra. The explicit
   `@IntermediateField.FG` merely specifies that canonical algebra instance.
6. For each maximal lower ideal n the existential upper ideal q is maximal and has
   `q.comap (eppNormalizationMap ...) = n`, exactly maximal-ideal surjectivity.
7. Conditional on `Module.Finite K P`, every lower residue has a finite canonical
   A-map, and every upper residue has a finite canonical B-map (`RingHom.Finite`).
   This is precisely finite extension over A/m_A and B/m_B: contraction to A or B
   is maximal by integrality of the corresponding closure, hence equals the unique
   maximal ideal. The residue action therefore factors through that quotient field.
   A generating family over A is a generating family over A/m_A and conversely;
   the same holds for B. This uses the specified structure maps and introduces no
   arbitrary residue-field algebra or extra hypothesis. `Ideal.ResidueField` is
   canonically the quotient for maximal ideals.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`,
  class signature and docstring at lines 56–60 (domain, local PID, not a field).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, class and docstring at lines 90–102.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, its real
  carrier and closure data at lines 213–224; `IsIntegral` and
  `IsIntegrallyClosedIn` were also read in their defining files.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, quotient construction
  and signature at lines 77–83. The Epp interface uses the commutative algebra tensor.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, lines 193–204.
- `Mathlib.RingTheory.FiniteType`: the recorded `RingHom.FiniteType` interface and
  `Algebra.FiniteType` (lines 36–40); this is used on the finite presentation U.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  lines 47–58. `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` supplies
  `Ideal.ResidueField` and its canonical `map`, lines 27–43. Their full signatures
  fix the ideal contraction and the residue map.
- `Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits`: `eppReducedTensor`,
  `eppUpperClosure`, `eppNormalizationMap`, lines 40–77. All three are real existing
  constructions and are attached by the new definition node below.

All original statement-dependency modules are public imports. All recorded proof
interfaces with modules, plus Mathlib leaf modules, are imported privately. The
source theorem's twelve proof steps and their dependency ids are included in its
new docstring. An eventual proof import from the Epp theorem module back to this
module would form an import cycle, since its definitions already live there; that
proof import must be omitted under stages/2-statements.md §3(7). This delivery does
not change the Epp module. The DAG definition node depends only on the foundational
notions, not on the downstream Epp theorem, so there is no DAG dependency cycle.

Edge cases checked: P=K recovers the original traits. A purely inseparable finite
extension may give tensor nilpotents, so reduction is essential and retained. The
zero ring and empty field product are excluded by positivity of the first t; neither
is an allowed input field. Dimension-one factors cannot be fields, because of their
nonzero-prime witness. Non-Nagata DVRs are allowed: no module-finiteness of their
normalizations has been added. In case (b), `B=(A[t])_(m_A A[t])` can have residue
extension k(t)/k, which is correctly permitted by field FG. Infinite algebraic P/K
is allowed exactly when the essential finite type presentation and lower
Noetherianity hold. When both cases apply both conditional residue conclusions are
available. No new statement is believed false; no STATEMENT-DISPUTED flag is needed.

Searches actually run with `msearch.py`:

- LeanFinder: "Structure of integral closures of a local extension of DVRs after
  algebraic reduced tensor base change semilocal normalization" returned localization
  of integral closure, dimension-LE-one and Dedekind ingredients, not this theorem.
- Loogle: `integralClosure, IsDiscreteValuationRing` returned zero hits.
- Mathlib grep: `integralClosure.*(dvr|DVR)|normalization.*structure|eppNormalizationMap`
  returned unrelated normalization-monoid hits.
- LeanSearch: "canonical ring homomorphism between integral closures after reduced
  tensor product of field extensions" returned `TensorProduct.toIntegralClosure`,
  `IsIntegralClosure.lift`, `AlgHom.mapIntegralClosure` and their lemmas, not this
  reduced generic tensor construction.
- LeanFinder: "The canonical map from integral closure of A in P to integral closure
  of B in reduced L tensor K P" returned the same generic ingredients.
- Mathlib grep: `eppReducedTensor|eppUpperClosure|eppNormalizationMap|nilradical.*TensorProduct`
  returned zero hits. Direct rg of `lean/WeilConjectures` found none of these helper
  names or the item id; rg of `lean/Sheaf` located the Epp module. DAG grep found the
  Epp theorem node's helper list, but no definition node for these constructions.
  `tools/blueprint_refs.py search normalization` and the ancestor query were run;
  the ancestor is null and no existing definition node matches this interface.

Validation: the module compiled through `scompile.py` against both the server's
sandbox import and library module modes with no errors or warnings. The first
compile diagnosed an argument-order mismatch in the explicit FG application; its
field/instance binder order was corrected. Every theorem proof is `sorry`.

## New nodes

`def-sfb-dvr-reduced-tensor-normalization-map` attaches existing definitions in
`Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits` rather than defining them again:
`IsDiscreteValuationRing.eppReducedTensor`, `.eppUpperClosure` and
`.eppNormalizationMap`. The definition states the reduced tensor, the actual
integral closure, and the canonical class of `1 ⊗ m`, with all maps and scalar
compatibilities specified. Source: Stacks Tags 09EM and 09IH, the normalization
diagram and the generic reduced tensor. Three actual search kinds, with raw result
records, are in `mathlib_searches`; Mathlib has generic integral-closure maps but
not this combined interface. Project grep found the existing real construction
listed by the Epp theorem node but no owning definition node. The new record uses
`existing: true`; no additional module, theorem or `sorry` is introduced for it.

Dry-run repair: the current server checker requires `import_flags: []` on new
definition nodes (stage2_delivery.py, field list updated 2026-10-23); this was
added. The existing signature record starts at the `def` keyword, excluding the
`noncomputable` modifier, as the source-signature extractor expects. Neither
repair changes mathematical content. The new definition's specialization sentence
also explicitly cites its DVR definition node.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
