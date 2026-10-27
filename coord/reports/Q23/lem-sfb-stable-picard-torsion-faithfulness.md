## Worker report

The delivery states `AlgebraicGeometry.StablePointedModuli.picard_torsion_faithfulness`
in `Sheaf.AlgebraicGeometry.StablePicardTorsionFaithfulness`. Its only theorem proof is
`sorry`; it introduces no definitions. The source was read at
https://numdam.org/item/AST_1985__127__131_0.pdf, printed pp.139--140,
Lemma 3.5.1. It explicitly treats a stable curve and invertible n at least three,
without a smoothness assumption or any condition on the order of its automorphism.
The original node statement and proof are unchanged.

Hypotheses and clauses, matched individually:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- Genus at least two is `(g : ℕ) (hg : 2 ≤ g)`.
- The stable unpointed genus-g curve is
  `C : Fiber (Spec (.of k)) g 0 (Over.mk (𝟙 (Spec (.of k)))))`.
  This is the dependency's actual groupoid fibre over Spec k, with zero ordered
  markings; its stability and geometric arithmetic genus are carried by the family.
- The actual curve over k is `fiberCurve C`, using the canonical transport of
  the projection along the base equality, without any choice of curve representative.
- The integer level is `(n : ℕ) (hn : 3 ≤ n) (hinv : IsUnit (n : k))`.
  Natural numbers encode exactly the integers satisfying the lower bound.
- The k-automorphism is `(a : Aut (fiberCurve C))`, an automorphism in the over category.
- `L : (fiberCurve C).left.Pic` is the existing isomorphism class of an invertible
  module; the existing Picard commutative group law is tensor product.
- Multidegree zero is the first antecedent of `hfix`, quantified over every
  `Z : irreducibleComponents (fiberCurve C).left`. Its normalization is the existing
  `reducedNormalizationComponent Z |>.normalization`; the map to the curve is
  `normalizedComponentMap Z`. `Scheme.Modules.pullback` pulls the representative
  `(fromSkeleton ...).obj L.val` to this normalization, and `Scheme.Modules.degree`
  computes its degree over k with structural map `normalizedComponentMap Z ≫
  (fiberCurve C).hom`. The equation is zero for each component separately, not merely
  zero total degree. Degree is invariant under isomorphism, so the representative
  makes no mathematical restriction on the class.
- The torsion condition is the second antecedent `L ^ n = 1`. In the recorded
  Picard group this says the n-th tensor power is isomorphic to the structure sheaf.
- `Scheme.Pic.map a.hom.left L = L` is precisely equality of pullback and original
  line bundle classes, required for every class satisfying those two antecedents.
- The conclusion `a = 1` is identity of the k-curve automorphism.
- Neither the order of a nor the order of Aut(C) occurs among the assumptions.
  There is no smoothness, irreducibility, separability or prime-level assumption.

Dependency declarations used (full signatures and docstrings read in source):

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic. The algebraic-closure node's mathlib_match
  specifically identifies the latter as its algebraically-closed-field predicate.
- `AlgebraicGeometry.StablePointedModuli` and `.Fiber`,
  Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids; its `genus`, `stable`,
  `base`, `projection` and actual-fibre encoding supply the family.
- `AlgebraicGeometry.StablePointedModuli.fiberCurve`,
  Sheaf.AlgebraicGeometry.StableFiberCurve, supplied by the already landed
  def-sfb-stable-fiber-curve; added that definition node to stmt_deps.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  WeilConjectures.AlgebraicGeometry.Modules.Invertible; the existing Picard
  implementation bridges its rank-one predicate with the sheaf predicate.
- `AlgebraicGeometry.Scheme.Pic`, `.map`,
  WeilConjectures.AlgebraicGeometry.PicardFunctor, and its tensor-product group
  `Scheme.Pic.instCommGroup`, WeilConjectures.AlgebraicGeometry.Picard.Group.
  Added the already landed def-sc-picard-group to stmt_deps.
- `AlgebraicGeometry.Scheme.Modules.degree`,
  WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar, definition chi(L)-chi(O);
  added the already landed def-pc-degree-line-bundle to stmt_deps.
- `Scheme.normalizedComponentMap`, Sheaf.AlgebraicGeometry.StablePointedCurve,
  imported through the recorded stable-moduli dependency; normalization is canonical.

Proof dependencies: the six-step natural-language proof from the node is included
in the theorem docstring. Five proof dependencies currently have no Lean record.
The sixth, lem-sfb-stable-isom-finite-unramified, still records the withdrawn module
Sheaf.AlgebraicGeometry.StableIsomFiniteUnramified. Its local file is absent and
`scompile.py --source Sheaf.AlgebraicGeometry.StableIsomFiniteUnramified` returned
`Module source unavailable: Sheaf.AlgebraicGeometry.StableIsomFiniteUnramified`.
Accordingly no absent proof module is imported. This does not affect the statement
interface; no proof dependency is asserted as an additional hypothesis. The owning
fiberCurve definition has already been restored independently and is used here.

Edge cases checked: g=2 and n=3 are included; composite n is allowed. In positive
characteristic only IsUnit(n:k) is imposed, so wild automorphism orders remain covered.
A nodal self-component and different irreducible components use their individual
canonical normalizations. Reducible compact-type curves and toric parts of generalized
Jacobians are retained. The trivial Picard class belongs to the torsion tested.
The empty curve cannot be a geometric stable curve (the recorded fibre convention is
connected and pure dimension one). No independent lower universe restricts fields or
curves; all schemes and the field share u, and the existing Picard lives in u+1.

Searches made on 2026-10-24:

- msearch.py leanfinder: “An automorphism of a stable curve is determined by its
  action on n torsion line bundles of multidegree zero for n at least three”.
  Eight hits on Galois-category automorphisms, cyclotomic characters and Weierstrass
  points; no stable-curve Picard faithfulness theorem.
- msearch.py loogle: `"Picard", "torsion"`: zero hits.
- msearch.py grep: `stableCurve|stable_curve|multidegree|Picard.*torsion`:
  one Weierstrass-model docstring concerning ring Picard 12-torsion; no theorem.
- msearch.py leansearch: “A stable curve automorphism acting trivially on Picard
  group n torsion is the identity”: eight hits, mostly ring Picard functoriality
  and semilocal Picard triviality; none states the item.
- rg over lean/WeilConjectures and lean/Sheaf for Picard, multidegree and
  normalized component degree found existing Picard classes, component maps,
  and degree. Read PicardFunctor, Picard/Group, Cohomology/EulerChar,
  StablePointedCurve, StableFiberCurve and AmpleIffNormalizedComponentDegreePos.
  Reused their constructions instead of defining a new Picard-zero group.
- rg for the item id in lean/WeilConjectures: no match. rg for the new declaration
  and module names in lean/Sheaf, lean/WeilConjectures and dag/lean_names_upstream.json:
  no existing match. No new notion or new DAG node is needed.

Validation: scompile.py compiled the delivered file as sandbox and library module,
3.0 and 3.1 seconds, respectively; no errors or warnings were printed.
No STATEMENT-DISPUTED issue, no statement correction, and no dependency-module repair.

## Second reading by Q23

This is a separate self-review pass, not a claim of an independent worker review;
the dispatcher's instruction prohibits starting other agents and says the maintainer
will independently review the delivery. Reopened the node and final Lean file.
Checked the field and algebraic closure binders; the g≥2 binder and genus-g zero-marking
actual fibre; n≥3 and IsUnit(n:k); over-category automorphism; existing Picard classes;
degree zero on every normalized reduced component; tensor n-torsion; pullback equality;
and identity conclusion, in that order. The class predicate uses the representative
only for degree, whose isomorphism invariance is the recorded degree_congr lemma.
The Picard group operations already identify tensor powers with the corresponding
powers of classes. Thus the two antecedents describe exactly Pic^0(C)[n].
No order or characteristic hypothesis beyond invertibility of n was introduced.
No missing clause or mismatch was found. Added explicit stmt_deps for the already
landed fibre-curve, Picard-group and degree definitions used in the signature.
The theorem signature in lean.statement is copied verbatim from the final file.
