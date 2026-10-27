## Worker report

The module Sheaf.AlgebraicGeometry.GenericComponentEtaleLocalSupport states
AlgebraicGeometry.genericComponent_etale_local_support with one sorry. Its helper
AlgebraicGeometry.genericComponentEtaleLocalIdeal constructs IB by Ideal.map of the
actual stalk homomorphism applied to the kernel of i.stalkMap η. The equality hw
transports the source stalk using TopCat.Presheaf.stalkCongr. It is a canonical
ideal extension, with real data and no postponed property or choice of a map.
This helper just names the composite construction appearing repeatedly in this node;
it introduces no independent notion requiring a new definition node.

The stage-1 Q69 PASS is the input split, not an existing Lean delivery. The live node
has no lean record and is in the stage-2 queue. The earlier stale-assignment ending
was resolved using brief-stage2 §0. No prior stage-2 delivery is present in the live
ledger/deliveries log. The saved sandbox draft and searches were retained.

The statement is unchanged. Its hypotheses and clauses correspond as follows:

| Node text | Lean rendering |
| --- | --- |
| Schemes X, Z, W | `{X Z W : Scheme.{u}}`, with explicitly declared universe u |
| X locally Noetherian | `[IsLocallyNoetherian X]` |
| Closed immersion i: Z → X | `(i : Z ⟶ X) [IsClosedImmersion i]` |
| Component C of Z | `(C : Set Z) (hC : C ∈ irreducibleComponents Z)` |
| η its generic point | `(η : Z) (hη : IsGenericPoint η C)`; this already implies membership |
| Étale v: W → X | `(v : W ⟶ X) [Etale v]` |
| w above i(η) | `(w : W) (hw : v w = i η)` |
| A, B, I, IB | `X.presheaf.stalk (i η)`, `W.presheaf.stalk w`, `RingHom.ker (i.stalkMap η).hom`, and `genericComponentEtaleLocalIdeal i η v w hw` |
| P = Z ×_X Spec B | `pullback i (W.fromSpecStalk w ≫ v)`; the second arrow is the canonical local-scheme morphism |
| dim O_Z,η = 0 | First conjunct `ringKrullDim (Z.presheaf.stalk η) = 0` |
| dim B/IB = 0 | Second conjunct, using the ideal quotient by the constructed extension |
| P ≅ Spec(B/IB), as a closed subscheme of Spec B | Existential `e` with `e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ...)) = pullback.snd ...`; the quotient spectrum map is the canonical closed immersion |
| P has exactly the point t | `∃ t, ∀ p, p = t`, asserting existence as well as uniqueness |
| t maps to the closed point s | `(pullback.snd ...) t = IsLocalRing.closedPoint (W.presheaf.stalk w)` |
| {t} the only irreducible component | `irreducibleComponents (pullback ... : Scheme.{u}) = {{t}}` |
| dim B = dim A | Penultimate conjunct equating the two stalk-ring dimensions |
| codim({s}, Spec B) = dim B | Last conjunct `Order.coheight` of s as a point of the scheme `Spec B`, coerced into `WithBot ℕ∞`, equals `ringKrullDim B` |

The type annotation `@id (Spec B) ...` in the last conjunct matters: a scheme carries
the specialization preorder, opposite the usual inclusion order on PrimeSpectrum B.
Thus coheight counts generalization chains starting at s, equivalently chains of
irreducible closed sets starting at {s}. This is the node's codimension convention,
not coheight of a prime in its ideal-inclusion order. Mathlib's
AlgebraicGeometry.ringKrullDim_stalk_eq_coheight (Tag 02IZ),
Scheme.le_iff_specializes, and irreducibleSetEquivPoints confirm this interpretation.
The final equality allows infinite Krull dimension. No local notation, private
instance, hidden let/show binder, reducedness or extra finite-presentation
hypothesis on the stalk-ring homomorphism is used.

Dependency declarations read and used:

- pqf-def-locnoeth: Mathlib.AlgebraicGeometry.Noetherian,
  AlgebraicGeometry.IsLocallyNoetherian.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  AlgebraicGeometry.IsClosedImmersion.
- def-sc-generic-point: Mathlib.Topology.Sober, IsGenericPoint.
- def-weil-irreducible-components: Mathlib.Topology.Irreducible,
  irreducibleComponents (mathlib_match, imported through Sober).
- def-weil-etale-morphism: Mathlib.AlgebraicGeometry.Morphisms.Etale,
  AlgebraicGeometry.Etale.
- def-weil-pbc-module-stalk:
  WeilConjectures.Topology.PresheafModuleStalkFunctor,
  PresheafOfModules.moduleStalkFunctor and its stalkObj/stalkMap declarations.
  The present statement only needs the ring-presheaf stalk carrier, the underlying
  TopCat.Presheaf.stalk already used by that recorded construction. Scheme.Hom.stalkMap
  gives the induced local ring homomorphism; no second stalk construction is defined.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  CategoryTheory.Limits.pullback and pullback.snd; scheme existence is supplied by
  the public Mathlib.AlgebraicGeometry.Pullbacks import.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  AlgebraicGeometry.Spec and Spec.map.
- def-weil-pbc-krull-dimension-ring: Mathlib.RingTheory.KrullDimension.Basic,
  ringKrullDim.

Proof imports include Mathlib.AlgebraicGeometry.Properties (02IZ),
Mathlib.RingTheory.LocalRing.Quotient, Mathlib.RingTheory.Localization.Ideal, and
WeilConjectures.RingTheory.Etale.LocalDimension
(RingHom.Etale.ringKrullDim_localization_eq). The existing étale-morphism import also
supplies the affine étale comparison and base change. The finite-intersection
étale stalk-model node has no recorded declaration; it is only a proof dependency,
not needed to type this statement, so no new declaration or dependency repair is
introduced for it. All six steps of the accepted proof appear in the theorem docstring,
with the DAG references explicitly named.

Sources read: literature/stacks-project/more-algebra.tex,
lemma-dimension-etale-extension (Tag 07QP), and properties.tex,
lemma-codimension-local-ring (02IZ) and lemma-generic-point (0BA9).
These give the two dimension comparisons and the generic-point/codimension facts
used in the unchanged accepted split.

Edge cases checked before finalizing the statement:

- Empty Z admits no η; the statement has no false existence conclusion there.
- Nonreduced Z is allowed: at the generic point of V(x²), the stalk can be Artinian
  with nilpotents. Dimension zero and singleton spectrum hold; being a field or a
  reduced point is never asserted.
- Reducible Z (for example V(xy)) allows either component and its generic point;
  localizing there removes the other component. No global irreducibility is required.
- i = identity makes I and IB zero; the conclusion then concerns the zero-dimensional
  local scheme above a component generic point.
- The quotient is nonzero because I is proper and the stalk map A → B is local;
  thus the existential point assertion is meaningful. B itself is a nonzero local
  ring as a scheme stalk, without additional hypotheses.
- Positive ambient dimension is retained: for a closed point in the affine line,
  dim B and the asserted codimension are both one, even though the support is one point.
- Neither finite global dimension nor a bound on dim A is imposed.

Searches (actual saved results are in sandbox searches.jsonl):

- msearch.py grep, `generic.*[Ee]tale|[Ee]tale.*ringKrullDim|codim.*closedPoint`:
  zero Mathlib hits.
- msearch.py loogle, `AlgebraicGeometry.Etale, ringKrullDim`: zero hits.
- msearch.py leanfinder, `An etale morphism over a generic point of a component of a
  closed subscheme gives a zero dimensional local quotient with singleton spectrum
  and preserves ambient local ring dimension`: eight hits concerning the étale
  locus, Algebra.IsEtaleAt, and standard smoothness; no full statement.
- msearch.py leansearch, `Etale morphism over generic component point of closed
  subscheme yields singleton local pullback and dimension zero quotient`: eight hits
  concerning Etale/IsEtale, étale ring maps and étale loci; no full statement.
- rg in lean/WeilConjectures and lean/Sheaf with the same conceptual patterns and
  both proposed declaration names: related generic-point and étale constructions,
  no declaration of this full conjunction and no duplicate proposed name.
- Search of lean/WeilConjectures for the item id: no hits.
- Search for existing kernel/stalk-map constructions found standard RingHom.ker,
  Ideal.map and stalkCongr combinations. These are used directly in the helper.

Validation: scompile.py compiled the module in both sandbox and library mode with
no errors or warnings. The first compile exposed ambiguous coercions for points of
the pullback; explicit Scheme.{u} annotations repaired them. No axioms, proof helpers,
new DAG nodes, dependency modules, statement corrections, or disputed statements.

## Second reading by Q59

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
