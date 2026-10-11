## Worker report

The node is already stated in the source repository by `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two` in `WeilConjectures.AlgebraicGeometry.Curve.Kummer`. Its hypotheses are an algebraically closed field, a curve morphism `f : C ⟶ Spec k` with `[IsCurve f]`, a natural number `n`, and `(n : k) ≠ 0`; these render “n > 0 invertible in k” and the curve assumptions. Its conclusion is `Nonempty (H²(C, μₙ) ≃+ H¹(C,Gₘ)/n)`, represented as the quotient of `C.CohomologicalPicardGroup` by the range of `zsmulAddGroupHom n`. The recorded `lem-sc-h1-gm-pic` declaration identifies this cohomological Picard group with `Pic(C)`, and the source proof uses `kummerδ₁` and Brauer vanishing, so the isomorphism is induced by the Kummer boundary.

Dependencies used: `def-sc-curves` (`AlgebraicGeometry.IsCurve`); `def-sc-kummer-sequence` (`Scheme.rootsOfUnitySheaf`); `def-sc-picard-group` (`Scheme.Pic`); `def-weil-pbc-etale-cohomology` (`Scheme.CohomologicalPicardGroup`); `lem-sc-h1-gm-pic` (`Pic.toCohomologicalPicardGroupAddEquiv`); and `lem-sc-brauer-zero-all-curves` (`IsCurve.subsingleton_cohomologicalBrauerGroup`). Edge cases in the source include n = 1, disconnected, singular, non-reduced, and zero-dimensional curves.

Searches: LeanFinder for second Kummer cohomology and Picard quotient found no exact Mathlib declaration; Loogle for Kummer/Picard quotient names found no exact match; `msearch.py grep` for `kummerδ₁|rootsOfUnitySheaf.*2` found the exact source declaration in `WeilConjectures/AlgebraicGeometry/Curve/Kummer.lean`. No module is written because the source declaration already exists.

## Earlier second reading (a previous round; superseded)

I read the node and the complete source declaration. Every hypothesis and the H²/Picard quotient conclusion matches. The source uses the cohomological Picard presentation of Pic(C), exactly the declaration recorded for `lem-sc-h1-gm-pic`; no extra case or hypothesis is introduced.

## Second reading by N1

I independently opened the sandbox node, the complete upstream Curve/Kummer.lean
statement and proof, the dependency nodes and the declarations listed below.
The earlier second reading was incorrect: the upstream theorem does not assert
that its equivalence is induced by the boundary, nor include the final vanishing
clause. A proof using a boundary is not a signature requiring that boundary.
I replaced the existing attachment with SecondKummerDivisors.lean, without changing
the mathematical node, its dependencies, or its proof.

Object/hypothesis/conclusion checklist against the node:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`; matches.
- Scheme C over k: `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))`; matches the explicit
  structure morphism used by the recorded IsCurve declaration.
- Curve: `[IsCurve f]`; Curve.lean defines this as separated, locally of finite
  type, quasi-compact, and topological dimension at most one. Thus finite type,
  with no smoothness, reducedness, connectedness, properness, or dimension-one
  assumption; matches def-sc-curves exactly.
- Integer n positive and invertible in k: `(n : ℕ) (hn : (n : k) ≠ 0)`; over a
  field this means precisely n > 0 and invertibility, including characteristic zero.
- μ_n: `C.rootsOfUnitySheaf n`, the kernel of `n • 𝟙 C.gmSheaf` in
  Sites/Kummer.lean; it is the first object of the recorded `C.kummerSequence n`.
- H²: `Sheaf.H (C.rootsOfUnitySheaf n) 2` on the small étale site. The source
  Sites/Gm.lean abbreviates H¹ and H² of gmSheaf as CohomologicalPicardGroup
  and CohomologicalBrauerGroup. I also opened the recorded Etale.cohomology in
  SixFunctors/Etale/Derived/LowerShriek.lean: homology of derived global sections;
  its docstring explicitly identifies sheaves in degree zero with sheaf cohomology.
  This delivery uses the source's existing abelian-sheaf cohomology API, as does
  the recorded Kummer sequence and Brauer-vanishing dependency.
- Pic(C)/n: `Additive C.Pic ⧸ (zsmulAddGroupHom ... (n : ℤ)).range`.
  PicardFunctor.lean defines Pic as invertible module classes in the skeleton;
  Additive changes notation for its tensor-product group law, not its objects.
  The quotient is precisely by n times that group.
- Displayed isomorphism: existential `e : H² ≃+ Pic/n`; matches, with the same
  orientation as the node. An additive equivalence asserts a group isomorphism.
- Induced by coboundary: for every invertibility proof hnC and Picard class L,
  `e (C.kummerδ₁ n hnC (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C L)) =
  QuotientAddGroup.mk L`. I opened both definitions in Sites/Kummer.lean and
  Sites/GmPicard.lean: kummerδ₁ is exactly Sheaf.H.δSucc of the Kummer short exact
  sequence; the Picard equivalence sends L to its Isom(O,L) torsor.
  This clause was missing in the worker's signature. Surjectivity of the quotient
  map makes this equality specify the induced inverse equivalence uniquely.
  The universal hnC is in the conclusion, not an extra hypothesis. Such a proof
  always exists: map hn.isUnit along ΓSpecIso.inv ≫ f.appTop and use map_natCast.
  Proof irrelevance makes the choice irrelevant; no proof is hidden in a definition.
- Final vanishing: `Subsingleton C.CohomologicalBrauerGroup`; matches H²(G_m)=0.
  This clause was also missing in the worker's signature. I opened
  IsCurve.subsingleton_cohomologicalBrauerGroup in Curve/Brauer.lean: same k,
  f and IsCurve hypotheses, no smoothness or properness assumption.

Source reading: the local repository lacks its literature files. I read the
Stacks TeX copy /home/ubuntu/c1-stacks-review/etale-cohomology.tex at
lemma-kummer-sequence (03PK) and lemma-cohomology-smooth-projective-curve (03RQ),
including the displayed long exact sequence in the latter's proof. 03PK assumes
invertibility on the scheme; 03RQ assumes smooth projective over algebraically
closed k. The node explicitly extends the boundary argument to arbitrary curves
using its separately cited all-curves Brauer vanishing, so the smooth projective
hypotheses must not be imported into this statement. The node's two proof steps
are reproduced in the new theorem docstring with all cited proof tools.

Edge cases: empty C is allowed (dimension bottom); both Pic and positive
cohomology vanish. Spec k and zero-dimensional components are included. No
index set is introduced. The zero Picard group and n=1 give zero quotient and
zero H². n=0 is excluded exactly as the node requires, even for empty C;
positive multiples of the characteristic are excluded by hn. Singular,
non-reduced and disconnected C are included. Universe u is arbitrary;
Picard classes and sheaf cohomology use the upstream Type (u+1) carriers,
with no extra smallness or finiteness hypothesis.

Independent searches: msearch LeanFinder query "Kummer connecting homomorphism
induces quotient Picard group second cohomology" found Selmer and group-cohomology
results, not this statement. Loogle `IsUnit.map` confirmed the invertibility
transport API. LeanSearch "Kummer sequence cohomology Picard quotient" was
unavailable (Internal Server Error), recorded without a search verdict.
rg for `kummerδ₁|kummer.*[Ee]quiv|[Ee]quiv.*kummer` in WeilConjectures and lean/Sheaf
found the upstream boundary definition and exactness statements, but no
boundary-compatible quotient equivalence; rg for Kummer, kummer and
CohomologicalPicardGroup in Mathlib/AlgebraicGeometry found none. I also searched
all three Lean trees for the new declaration name: no collision. Existing
upstream exactness and abstract equivalence statements are used as proof tools,
not redefined. No new notion, new definition node, or dependency module is needed:
all objects and maps occur in the dependency/source APIs already opened.

The recorded lem-sc-h1-gm-pic primary name is only the H¹ abbreviation, not the
canonical group identification claimed in the worker report; its audit also
lists the actual Pic.toCohomologicalPicardGroupAddEquiv, which I opened and used.
The worker's description of def-weil-pbc-etale-cohomology as that abbreviation
was also inaccurate; the checklist above gives its actual declaration.

Validation: scompile.py N1 lem-sc-second-kummer-divisors on the new module
returned exit code 0, compiled in 4.3 seconds, with no warnings. All universes
and variables are explicitly bound. There is no new definition, no hollow
object, and the only theorem proof is sorry. The node lean.statement is extracted
verbatim from the module signature. No statement correction, new nodes or
dependency modules were delivered.
