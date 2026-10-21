## Worker report

Item: lem-sfb-coefficient-diagram-regular-scalars. The module
Sheaf.CategoryTheory.ModuleObjects.CoefficientDiagramRegularScalars states the
node in three named theorem clauses, each with `sorry`: global scalar
multiplication as a regular-module endomorphism, the coefficient component's
ring compatibility for sequential transport, and the normalized coefficient
comparison with scalar intertwining. There are no proofs and no hollow data.
The two transparent abbrevs only apply the existing extension functor and
balancing projection, supplying their smallest-colimit instances from the
full preservation hypotheses. They introduce no alternative construction.
No node statement, dependency list, or proof has been changed.

Hypothesis and clause correspondence:

- C, D, E are independently universe-polymorphic categories with
  MonoidalCategory and BraidedCategory instances. All six object/morphism
  universe parameters are explicitly declared; autoImplicit is disabled.
- E has `HasCoequalizers E`, and the two families
  `PreservesColimits (tensorLeft X)` and `PreservesColimits (tensorRight X)`.
  The adapters call `preservesSmallestColimits_of_preservesColimits` to feed
  the existing API without weakening these hypotheses to finite colimits.
- P, Q, F have exactly the stated domains and codomains, and `P.Monoidal`,
  `Q.Monoidal`, `F.Monoidal` give the strong monoidal structures. No functor
  is required to be braided, exact, faithful, or colimit-preserving.
- The comparison is `c : P ⋙ F ≅ Q` with `NatTrans.IsMonoidal c.hom`.
  Mathlib's composition order is diagrammatic, so this is F after P.
- Λ has `MonObj Λ` and `IsCommMonObj Λ`. R, T, S are the literal objects
  `P.obj Λ`, `F.obj (P.obj Λ)`, `Q.obj Λ`, with scoped `Functor.monObjObj`
  structures and the three separately assumed commutativity instances.
- α is `c.hom.app Λ`, with inverse `c.inv.app Λ`. The theorem instance
  `coefficientDiagram_isMonHom` explicitly selects `F.monObjObj (P.obj Λ)`
  and `Q.monObjObj Λ`; Mathlib then supplies preservation for its inverse.
  This avoids accidentally selecting the transported structure of P ⋙ F
  where the node prescribes sequential transport.
- H is `F.mapMod (P.obj Λ) ⋙ coefficientDiagramExtension (c.hom.app Λ)`.
  The latter is an abbrev for the recorded `Mod.extendScalars`, with only
  the universe-size instances supplied explicitly.
- A scalar is `a : 𝟙_ C ⟶ Λ`; a_R and a_S are written out as
  `Functor.LaxMonoidal.ε P ≫ P.map a` and the corresponding expression for Q.
- `regularScalar_eq_leftMultiplication Z b` identifies the existing typed
  endomorphism `Mod.regularLift (Mod.regular Z) b` with the exact left-unitor
  formula `(λ_ Z).inv ≫ b ▷ Z ≫ μ[Z]`. It applies to any commutative Z,
  in particular Λ, R, T, S. Thus no linearity hypothesis has been inserted.
- The first two scalar conjuncts give exactly P(t_a)=t_aR and Q(t_a)=t_aS
  with the full left multiplication expressions. The third gives the α/F
  scalar square, with Lean's diagrammatic composition order.
- The first existential gives the transported regular module isomorphism i
  and requires both underlying maps to equal the identity of T.
- The second existential gives an S-module isomorphism e from H(R) to S.
  Its first two conjuncts are exactly q followed by e equals S ◁ α followed
  by μ_S, and e inverse equals the ambient right unitor inverse followed
  by S ◁ η_T followed by q. `coefficientDiagramProjection` is literally
  `Mod.extendπ` on the transported regular module, with its sequential
  MonObj structure explicitly selected.
- The `∀ a` is inside the existential for e: the same e satisfies scalar
  intertwining for every scalar. The final equation is in Mod E S; its
  image under the faithful forgetful functor is the requested ambient
  equation. The q formulas already are equations of E morphisms.

Dependencies read and used:

- Mathlib.CategoryTheory.Monoidal.Category: `MonoidalCategory` (def-sfb-monoidal-category).
- Mathlib.CategoryTheory.Monoidal.Functor: `Functor.CoreMonoidal`, and its
  equivalent class interface `Functor.Monoidal` (def-sfb-strong-monoidal-functor).
- Mathlib.CategoryTheory.Monoidal.Mon: `Functor.monObjObj`, `mapMon`,
  `mapMonNatIso`, `mapMonCompIso`, `MonObj`, `IsMonHom`.
  These are the recorded det-def-sfb-ring-object-transport constructions.
- WeilConjectures.CategoryTheory.RingObjects.RingPresheaf publicly supplies
  the recorded sk-def-sfb-ring-object interface; the abstract clauses use
  `MonObj`, `IsCommMonObj`, and `IsMonHom`, rather than a cartesian RingObj.
- WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod: `Functor.mapMod`,
  `Functor.modObjObj`, `Functor.act_mapMod_obj` (def-sfb-modobj-transport),
  and the already constructed `Mod.regularLift` for typed regular maps.
- Mathlib.CategoryTheory.Monoidal.Mod: `Mod`, `ModObj`, `Mod.Hom`,
  `Mod.regular` (sk-def-sfb-module-objects).
- WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars:
  `Mod.extendScalars`, `Mod.extendπ`, `Mod.extendScalarsObj_X`,
  `Bimod.ofMonHom` (def-sfb-modobj-extension).
- Proof dependencies are imported through these public modules and the
  proof-only import Mathlib.CategoryTheory.Monoidal.Free.Coherence:
  `BraidedCategory.braiding_naturality`, `braiding_leftUnitor`,
  `FreeMonoidalCategory.subsingleton_hom`, `Bimod.rightUnitorBimod`, and
  `Limits.colimit`/`IsColimit`. Their signatures and docstrings were read.

Edge cases checked before writing: no zero scalar hypothesis; the unit
scalar is included; categories without additive structure are allowed;
no braiding-preservation hypothesis on P, Q, F; no equality of S and T;
no purity-of-sections assertion; independent universes for all categories;
the same e must work for all a. Existence of Λ and the tensor unit already
makes empty underlying categories irrelevant, without adding Nonempty.
The generic scalar theorem requires only the structure its clause needs.
No STATEMENT-DISPUTED issue or correction was found.

Searches for an existing statement (2026-10-21):

- msearch.py leanfinder: "A monoidal natural isomorphism between composite
  strong monoidal functors identifies extension of scalars of regular modules
  and intertwines scalar multiplication". Eight hits: ordinary ModuleCat
  change-of-rings comparisons and Mod_.scalarRestriction_smul; no abstract
  coefficient-diagram statement with normalized balancing formulas.
- msearch.py loogle: `"rightUnitorBimod"`. Seven hits: the mixed-bimodule
  unitor and its component lemmas. This supplies a proof constituent,
  not the functor/scalar transport clauses.
- msearch.py grep: `mapModUnitIso|regularExtensionIso|coefficientDiagram`
  in CategoryTheory: zero Mathlib hits.
- rg of WeilConjectures and Sheaf for the item and comparison names found
  MapModMonoidal.mapModUnitIso (requires braided F and colimit assumptions
  on D), RegularExtensionComparison.regularExtensionIso (no diagram or
  balancing normalization), and consumer modules. None states this node.
  The existing regularLift was reused rather than copied.
- rg of both library roots for every new declaration name found no clash.
  The search wrapper's verbatim results are retained in searches.jsonl.

Validation: scompile.py compiled both sandbox and library module forms cleanly.
Only the three named statement clauses are postponed. Each has this node's
blueprint tag, source, and a natural-language proof. The live repository was
only read; all packet edits are inside the assigned sandbox.

## Second reading by Q47

I reopened the node and the completed file for a separate self-check; this
is not an independent-agent review (the dispatcher forbids starting agents).
The maintainer's independent review remains required. The check found the
composite-versus-sequential MonObj distinction and fixed it by explicit
instance arguments, rather than adding a ring-map hypothesis. It also
restored the full colimit-preservation assumptions after an early compile
attempt used the smallest-size assumptions directly. The adapters now pass
those derived smallest-size instances to the recorded functor and projection.
The scalar comparison, identity regular-module identification, both q
normalizations, and final all-scalars equation match the clauses above.
The all-scalars quantifier is inside the one existential e; no scalar-dependent
choice or arbitrary replacement of the balancing map is used.
