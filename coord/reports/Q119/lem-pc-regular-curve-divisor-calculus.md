## Worker report

Q119 states `AlgebraicGeometry.Scheme.regular_curve_divisor_calculus` in
`lean/Sheaf/AlgebraicGeometry/RegularCurveDivisorCalculus.lean`. Its sole proof is `sorry`.
No construction is chosen from an existence theorem and no new definition is introduced.
The existing general valuation-bounded divisor module is reused. The statement-dependency
list gains its already landed node `def-sc-divisor`, as permitted by brief-stage2 §5
(STMT_DEPS MAY GAIN LANDED NODES). Every other pre-existing node field is unchanged.

Hypotheses and objects:

- `X : Scheme.{u}` and `[IsIntegral X]` give the arbitrary integral scheme, its nonemptiness,
  generic point `genericPoint X`, and field `X.functionField`, literally its generic stalk.
  There is no field of definition or morphism to a field spectrum in the statement.
- `[IsNoetherian X]` is Mathlib's class extending both `IsLocallyNoetherian X` and
  `CompactSpace X`. This is exactly the node's explicit meaning of Noetherian.
- `[IsRegular X]` asserts regularity of every local ring. Together with the local
  Noetherianity already supplied, this is precisely the recorded predicate
  `IsRegularScheme X := IsLocallyNoetherian X ∧ IsRegular X`; it adds no assumption.
- `hdim : X.dim = 1` uses the recorded local-ring-supremum dimension, not an assumption of
  finite type or a separate relative-dimension predicate.
- `closedPoints X` supplies all closed points. `X.Divisor` is the existing finite-support
  function type `closedPoints X →₀ ℤ`, so it is exactly the finite formal sums in the node.
- `D.associatedModule X` is the existing explicit valuation-bounded module. Its sections
  are locally constant functions `U → X.functionField`, including zero, satisfying
  `0 ≤ X.ord (s x) x.val + D x` for each nonzero value at a closed point. Since X is
  irreducible, any nonempty open is irreducible and these functions are constant. Thus this
  is the node's subsheaf of the constant rational-function sheaf. On the empty open there
  is exactly one function, the zero module. This construction is defined for the present
  arbitrary regular integral Noetherian scheme; the smooth-curve wrapper is not used.

Clause-by-clause rendering:

1. The first conjunct gives `IsDiscreteValuationRing (X.presheaf.stalk x.val)` at every
   closed point. Its equivalence `X.ord f x.val = n ↔ ∃ t, maximalIdeal = Ideal.span {t} ∧
   ∃ a : (...)ˣ, f = algebraMap a * (algebraMap t)^n` identifies `ord` with the stated
   normalized valuation. The uniformizer and unit are actual elements of that local ring,
   and powers are integer powers in the function field. The original `ord` already has
   product additivity; no independent valuation is substituted.
2. Part (1), invertibility, is `∀ D, (D.associatedModule X).IsInvertible`.
   `O(0)=O_X` is an isomorphism to `SheafOfModules.unit X.ringCatSheaf` with its generic-germ
   formula: the image of a rational section has exactly that rational value. This records
   equality as subsheaves of K despite their different bundled representations.
   The next conjunct gives `D.associatedModule X ⊗ E.associatedModule X ≅
   (D+E).associatedModule X`. Its formula on every open and pure tensor says the image
   evaluates at y to `a.val y * b.val y`. The pure tensor is sent into the sheaf tensor
   using the existing sheafification-adjunction unit and `tensorObjIsoSheafification`.
   Thus the asserted isomorphism is the multiplication morphism, not an arbitrary iso.
3. Part (2) quantifies over every `L : X.Modules` with `[L.IsInvertible]`. The existence
   `∃ s : ↑(TopCat.Presheaf.stalk ... (genericPoint X)), s ≠ 0` supplies a nonzero rational
   section. For every such s, `∃! D : X.Divisor` specifies its finite divisor.
   For every closed x and every generator e (`Submodule.span (...) {e} = ⊤`), a unit
   `f : X.functionFieldˣ` expressing s as f times the specialized generator exists.
   For EVERY such coefficient, `D x = X.ord f x.val`. Quantification over all generators
   proves generator independence; membership of D in the Finsupp type supplies finite
   support. The divisor is therefore specified entirely by the coefficient formula and
   not by an unspecified choice of line-bundle representative.
4. The same conjunct supplies `e : D.associatedModule X ≅ L`. For every U containing the
   generic point and every rational section a, the generic germ of `e(a)` equals
   `a(η) • s`. This is exactly multiplication by s. Generic germs determine sections of
   an invertible module on an integral scheme, so this condition specifies the actual map.
   For every global section with generic germ s, `∀ x, 0 ≤ D x` gives effectivity.
   The final clause for L states explicitly that a nonzero global section has nonzero
   generic germ, so the preceding assertion applies to every nonzero global section.
5. The principal case uses the existing `X.div (Additive.ofMul f)` for each unit f in K.
   Its isomorphism to the structure sheaf has generic formula `a(η) * f`; it is therefore
   the asserted principal-divisor trivialization with the correct sign.
6. Part (3) quantifies over every D and closed x. It supplies
   `V : ModuleCat.{u} (X.residueField x.val)` with `Module.finrank ... V = 1`.
   The skyscraper is exactly `ringedModuleSkyscraper X.toRingedSpace x.val` applied to V
   restricted along `(X.residue x.val).hom`; hence the local-ring action factors through
   its residue field, as required. The source of i is `(D - Finsupp.single x 1).associatedModule X`,
   its target is `D.associatedModule X`, and its value at every y is unchanged as a rational
   function. Thus i is the natural inclusion. There is a map q to this skyscraper and
   `∃ w : i ≫ q = 0, (ShortComplex.mk i q w).ShortExact`, the displayed sequence including
   exactness and the two zero end terms. The final `Nonempty` iso identifies this same
   skyscraper with the skyscraper of the residue field itself, without choosing a basis
   as part of the hypotheses. No canonical identification with the residue field is asserted.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, and `IsNoetherian`, whose
  parents express precisely the node's locally-Noetherian and compact hypotheses.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, the other Noetherian parent.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`, read with
  `WeilConjectures.AlgebraicGeometry.Regular`: `AlgebraicGeometry.IsRegular`.
- `WeilConjectures.AlgebraicGeometry.Dimension`: `Scheme.dim`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the integral-scheme clause of
  `def-sc-function-field` is explicitly delegated to Mathlib `Scheme.functionField`;
  the component-product definition is not used for this integral-scheme assertion.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing` and the
  uniformizer criterion `maximalIdeal = Ideal.span {t}`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and `Scheme.residue`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded tensor
  interface, which is the existing localization tensor; the scheme monoidal instance and
  `SheafOfModules.tensorObjIsoSheafification` are used for local pure tensors.
- `WeilConjectures.Topology.RingedModuleSkyscraper`: `SheafOfModules.ringedModuleSkyscraper`,
  the object construction underlying the recorded `ringedModuleSkyscraperFunctor`.
- Added, already landed `def-sc-divisor`: `Scheme.Divisor`, `Scheme.div`, and
  `Divisor.associatedModule`. The recorded Sheaf module and the published upstream module
  have these same declarations and general signatures. Following the launcher's explicit
  upstream-preference instruction, import `WeilConjectures.AlgebraicGeometry.DivisorModule`.
  I also read its current server source with `scompile.py --source` and confirmed the
  general construction and exact valuation bounds. No replacement definition is made.

Proof-dependency modules with recorded statements are imported without `public` unless
already part of the public statement imports. These include the finite-complement theorem,
the local-ring dimension comparison, integral function-field gluing, regular-dimension-one
DVR criterion, presheaf module stalks, coherent finite-type interface, and stalkwise exactness.
The declaration docstring carries all ten natural-language proof steps from the node,
including the non-separated finite-complement argument and the local quotient calculation.

Sources checked: `literature/stacks-project/divisors.tex`, definitions and proofs at
`definition-invertible-sheaf-effective-Cartier-divisor` (01WX),
`definition-order-vanishing-meromorphic` (02SF), `lemma-c1-additive` (02SL),
`lemma-normal-c1-injective` (0BE8), and `lemma-local-rings-UFD-c1-bijective` (0BE9).
The generality of the node is consistent with those places; no correction is required.

Edge cases checked: the empty open gives the zero module in the existing construction;
X itself cannot be empty by integrality or have dimension zero by hdim. D=0 gives the
structure sheaf; positive and negative point coefficients have lattices t^(-n)R, and the
subtracted point has t^(1-n)R, so the quotient is one-dimensional with the stated sign.
On Spec of a DVR the generic-only open has no closed-point bounds, as required.
No closed-point rationality, algebraic closure, properness or separatedness was used:
in particular a doubled-origin integral regular Noetherian curve is included. The zero
rational section is excluded only in part (2); zero global sections and zero rational
functions remain valid sections of every divisor module. Every universe is bound explicitly.

Duplicate searches, with the actual wrapper queries and results:

- `msearch.py ... leanfinder "Regular integral Noetherian scheme dimension one divisor sheaf
  rational section invertible module skyscraper exact sequence"`: eight hits on
  `Scheme.functionField`, its field and fraction-ring instances, and related affine facts;
  none states the divisor-calculus theorem.
- `msearch.py ... loogle "Scheme.functionField, Divisor"`: unknown identifier
  `Scheme.functionField`, zero hits. Repeated with `"divisor", "invertible"`: zero hits.
- `msearch.py ... leansearch "regular curve invertible sheaf divisor module rational section"`:
  eight hits on `ModuleCat.Tilde` sections/restrictions and `StructureSheaf` basic opens;
  none states this theorem.
- `msearch.py ... grep "divisorModule|rationalSection|normalizedValuation" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for divisor modules and rational sections
  found the general `Divisor.associatedModule`, which is reused, and the smooth connected
  algebraically-closed-field statements `rational_section_order`, `rationalSectionDivisor`,
  `Divisor.module_local`, and `nonempty_module_tensor_add_iso`. I read their complete
  relevant declarations and docstrings. Their smooth-curve hypotheses do not state this
  arbitrary regular-curve theorem. `grep -rn` for this item id in `lean/WeilConjectures`
  and `rg` for the proposed full theorem name in Mathlib, WeilConjectures and Sheaf gave
  no existing declaration.

Validation: the prescribed server compiler accepted both sandbox and actual library module
names with no errors or warnings (22.1 s and 21.7 s, before adding explicit dependency
import lines). The sole postponed theorem uses `sorry` as required. All lines are at most
100 characters. Final validation is the prescribed deliver2 preflight and per-file compile.
No STATEMENT-DISPUTED flag or statement correction is needed.

## Second reading by Q119

I reread the node, each dependency interface, and the complete generated signature in a
separate pass; this is a worker self-check, with the maintainer's independent review still
to follow as specified in the dispatcher brief. No other agent was started.
The three structural assumptions and dimension binder exactly match the opening sentence.
The first valuation conjunct connects the chosen existing ord to unit-times-uniformizer
powers. I checked that the point generator criterion is equality with the maximal ideal,
not merely membership in it, and that negative exponents are integer powers in K.
The invertibility, zero-divisor and tensor clauses all concern the same explicit
`associatedModule`; the maps are constrained by their rational multiplication formulas.
The rational-section clause uses every generator and every coefficient, finite-support
D, and a multiplication isomorphism. Nonzero global germs and effectivity are both
present, including the principal-function specialization. The quotient clause uses the
same D, subtracts exactly one copy of the chosen closed point, and constrains i to the
natural inclusion. It supplies a one-dimensional residue-field module with the correct
restricted stalk action, a genuine short exact sequence, and the final noncanonical iso.

The compiler exposed two presentation defects in the first draft: stalk objects used as
types needed the explicit coercion `↑(...)`, and the live `tensorObjIsoSheafification`
expects its coefficient sheaf as implicit parameter `(R := X.sheaf)`. Both were corrected
and the entire declaration compiled cleanly. This changes no mathematical hypothesis or
clause. No mismatch with the node remained in the second reading.
