## Worker report

The module defines `AlgebraicGeometry.Scheme.functionFieldOfComponents`. For a scheme `X`, its
underlying type has the set `TopologicalSpace.irreducibleComponents X`; the definition indexes a
dependent product by the subtype of these components. For each component `Z`,
`Z.property.1` is its `IsIrreducible` proof and `(Z.property.1).genericPoint` is the canonical
Mathlib generic point supplied by sobriety. The product entry is the structure-sheaf stalk
`X.presheaf.stalk (Z.property.1.genericPoint)`, and `CommRingCat.of` gives the product ring.
Specializing `X` to the curve `C` in the node gives the displayed product
`O_{C,eta_1} × ... × O_{C,eta_n}`. The definition also applies to the more general integral-scheme
clause of the node (where the product has one component).

The node's hypotheses and clauses are rendered as follows. `C` and its curve-over-`k` hypotheses
are the intended specialization of the explicit scheme parameter `X`; `irreducibleComponents X`
implements the cited component notion; the subtype binder supplies every component `C_i`; and
`Z.property.1.genericPoint` supplies each `eta_i`, using Mathlib's `IsIrreducible.genericPoint`.
The stalk expression is exactly the structure-sheaf stalk from `def-weil-pbc-module-stalk`.
Finiteness, the rational-function-ring identification, and the integral field-of-fractions
properties are theorem clauses cited by the node (`lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-noetherian-finite-components`, `lem-sc-rational-functions-generic-stalks`, and
`lem-sc-integral-function-field-affine-fraction`); they are not data hidden in the definition.

Dependency declarations used: `AlgebraicGeometry.IsCurve` from
`WeilConjectures.AlgebraicGeometry.Curve`; `TopologicalSpace.irreducibleComponents` from
`Mathlib.Topology.Irreducible`; `TopologicalSpace.IsGenericPoint` and
`TopologicalSpace.IsIrreducible.genericPoint` from `Mathlib.Topology.Sober`; scheme stalks
`Scheme.presheaf.stalk` from `Mathlib.AlgebraicGeometry.Properties`; and
`AlgebraicGeometry.IsIntegral` / `Scheme.functionField` conventions from
`Mathlib.AlgebraicGeometry.Properties` and `Mathlib.AlgebraicGeometry.FunctionField`.

Edge cases checked: the dependent product is valid for an empty scheme (empty index), for a
zero-dimensional curve, and for reducible curves; no irreducibility or nonemptiness instance is
assumed. For an integral scheme the component subtype is propositionally a singleton, recovering
the sole generic stalk. Universes are explicit (`universe u`, `Scheme.{u}`, `CommRingCat.{u}`).

Searches for an existing declaration: `msearch.py ... leanfinder "function field of a scheme:
product of stalks at generic points"` found only `Scheme.functionField` for irreducible schemes;
`msearch.py ... loogle "Scheme.functionField, irreducibleComponents, genericPoint"` found the
same Mathlib declarations; grep of Mathlib `FunctionField.lean` found only the irreducible
stalk definition and fraction-ring theorem; `rg functionField` in `WeilConjectures/` found no
reducible-curve product definition; and `rg functionField` in `lean/Sheaf` found no matching
notion. Thus no existing declaration says the node's reducible product.

## Earlier second reading (a previous round; superseded)

Reading the node and module together: the component subtype corresponds clause-for-clause to
`C_1, ..., C_n`; `Z.property.1.genericPoint` is the unique generic-point construction used for
`eta_i`; and the dependent product wrapped by `CommRingCat.of` is the stated product of stalks.
The source's later equivalences are explicitly delegated to the cited lemma nodes. No hypothesis
is added to the definition, no component is omitted, and empty and reducible cases remain
included.


## Second reading by E1

I read the node copy and module, every statement dependency and its recorded declaration,
Mathlib FunctionField.lean, Sober.lean, Irreducible.lean, Properties.lean and the relevant
Noetherian.lean declarations, and the landed RationalFunctionRing.lean and
RationalFunctionsGenericStalks.lean modules. This is a definition node: its proof is empty;
the explanatory theorem clauses belong to the explicitly cited lemma nodes, not additional
proof obligations to copy into this module.

Object/hypothesis/clause checklist:

1. A curve C over k: Scheme.functionFieldOfComponents accepts its underlying scheme X.
   IsCurve in WeilConjectures.AlgebraicGeometry.Curve extends separatedness, locally finite
   type and quasi-compactness and has dimension at most one. The node refers to algebraically
   closed k via def-sc-curves; the product is independent of the base field and does not need
   its structure morphism. Accepting arbitrary X does not alter the value on any such C and
   asserts no theorem for schemes outside the node's hypotheses. Verdict: correct definition
   with deliberately reusable domain, not a stronger theorem.
2. All irreducible components C_i: the subtype
   {s : Set X // s ∈ irreducibleComponents X} uses the dependency's actual maximal
   IsIrreducible subsets, not connected components, a chosen covering, or reduced subschemes.
   Verdict: exact, with indexing independent of the enumeration.
3. Generic point eta_i in each component, existence and uniqueness: Z.property.1 is its
   irreducibility proof; its genericPoint chooses a point with singleton closure closure Z.
   isClosed_of_mem_irreducibleComponents gives closure Z = Z. The actual scheme instances
   QuasiSober and T0Space in Properties.lean give existence and uniqueness; IsGenericPoint.eq
   identifies this choice with every eta_i of the node. Verdict: exact.
4. Finitely many components: a field spectrum is Noetherian; finite type in IsCurve gives
   local Noetherianity and compactness by the two recorded finite-type dependency declarations.
   finite_irreducibleComponents_of_isNoetherian yields finiteness. The definition needs no
   Fintype choice and its dependent product is the same finite product on a curve. Verdict:
   the node's explanatory finiteness clause is covered by its cited dependencies.
5. Structure-sheaf stalks and product ring k(C): X.presheaf.stalk at each chosen generic
   point is the scheme's actual CommRingCat stalk, using TopCat.Presheaf.stalk from the stalk
   dependency. CommRingCat.of wraps the dependent function type with pointwise ring operations.
   Verdict: exact; factors are stalks, not residue fields (important for nonreduced C).
6. R(C) identified by the germ map: the recorded dependency is now
   Scheme.rationalFunctionRing, the arbitrary-universe colimit of denseOpenSections.
   Scheme.rationalFunctions_generic_stalks quantifies over Fin n equivalences with exactly
   this component subtype and IsGenericPoint witnesses. It states the dense-open membership,
   ring equivalence and its values on every section coprojection. Taking eta_i to be the
   chosen points and reindexing its product gives this definition's carrier. Verdict: the
   same identification with the same map, supplied by the cited lemma, not a second notion.
7. Integral curve has one component, itself, and a field generic stalk: IsIntegral in
   Properties.lean is nonempty with domain sections, equivalent to irreducible and reduced.
   The integral clause of rationalFunctions_generic_stalks states n = 1, all components univ,
   and IsField of each generic stalk. Verdict: exact via the existing dependency.
8. Every nonempty affine open gives its field of fractions through germs:
   functionField_isFractionRing_of_isAffineOpen takes [IsIntegral X], U, IsAffineOpen U and
   [Nonempty U], and states IsFractionRing Γ(X,U) X.functionField. The Algebra is induced by
   Scheme.germToFunctionField; its field instance and injectivity theorem were read too.
   Evaluation on the sole component identifies the product with this same stalk. Verdict:
   exact; no hypothesis of affine X or finite type X has been imposed.
9. Arbitrary integral scheme X: reuse Mathlib's existing Scheme.functionField, defined as
   X.presheaf.stalk (genericPoint X), rather than inventing another integral function field.
   The previous report's word "recovering" means canonical ring isomorphism: the dependent
   product is not definitionally that stalk. Verdict: exact with this clarification; no
   additional definition is needed for this clause.

Edge cases: the empty scheme has no components, hence the empty product is the one-element
zero ring; n = 0 in the generic-stalks dependency permits this. No Field or nontriviality
instance is asserted for that product. Zero-dimensional, disconnected, reducible and
nonreduced curves remain included. Integral implies nonempty, as required for its field
clause. No characteristic restriction is used. Scheme.{u}, its sets/component subtype,
stalks and the product all lie in the same arbitrary explicit universe u; no auto-implicit
variable or unbound universe remains. No choice of enumeration changes the ring up to its
canonical reindexing isomorphism.

Independent searches: msearch LeanSearch query "ring of meromorphic functions of a reducible
scheme as the product of its generic local rings" returned service unavailable (Internal
Server Error), so I make no negative-result claim for that service. Loogle query
"AlgebraicGeometry.Scheme.functionField" returned Scheme.functionField, the field and
fraction-ring instances, germToFunctionField and its injectivity theorem; none defines the
component product. msearch grep "meromorphic|total.?quotient|functionFieldOfComponents" in
Mathlib AlgebraicGeometry returned zero hits. Independent rg for functionField/rationalFunction
in upstream curve modules found only constructions using the irreducible functionField.
Independent rg for functionFieldOfComponents and product/stalk combinations throughout
WeilConjectures and lean/Sheaf found no matching definition; the generic-stalks theorem
already states the identification but does not define the product as a named ring.
I also checked dag/lean_names_upstream.json: no component-product declaration is recorded.

Mismatches/repairs: the ring expression and node signature were correct and left intact.
The module lacked the standard copyright header. Its documentation did not explain the
closedness needed by IsIrreducible.genericPoint, the reuse of Scheme.functionField for the
integral-scheme clause, or the separation of the cited equivalence properties from the
product definition. I added the header and these explanations, with the exact Stacks places
01RV/01RW, and clarified the Lean record's note. No node statement correction, new node,
dependency replacement, proof, private definition, or hollow data was introduced.

Source reading: I read the original blueprint Markdown at the node's recorded path on the
project server: it defines precisely the product, its rational-function-ring equivalence,
and the integral affine fraction-field description. I read Stacks morphisms.tex from its
upstream raw source at definition-rational-function, definition-ring-of-rational-functions,
lemma-integral-scheme-rational-functions and definition-function-field (01RT/01RU/01RV/01RW),
and the source server's opening of section-rational-maps: the only ambient assumption is
that X is a scheme. The product calculation assumes finitely many components; its integral
field clause assumes integral, with no separatedness, finite type or base field restriction.
This agrees with the node and the dependency signatures. No statement_change is present,
so there are no corrected citer verdicts to audit. No new nodes or dependency modules occur
in this delivery. scompile.py compiled the edited module cleanly in 1.8 seconds, with no
warnings, errors or sorry declarations.
