## Worker report

The module `Sheaf.CategoryTheory.DgAbcConeHomotopy` states the node theorem
`CategoryTheory.IntegralDGCategory.ABC.dg_abc_cone_homotopy`.  It reuses the
published integral dg-category, shifts, admissible sequences, cones, and axiom-A
interfaces from `Sheaf.CategoryTheory.DgAbcData`; it introduces the canonical
zero-degree composite transport `compZero` to cast the degree `0 + 0` output of
`IntegralDGCategory.comp` to degree zero.  No definition uses `sorry`; the sole
postponed proof is the theorem proof required by stage 2.

The hypotheses are rendered as follows.  `A` is an
`IntegralDGCategory.{u,v}` over the integers; `S : Shifts A` is the complete
shift datum (strict object and arrow shifts, shifted Hom isomorphisms and their
composition signs); `hA : AxiomA A` is the dg zero object and dg biproduct
axiom; and `hC` supplies a `Nonempty (Cone S f)` for every closed degree-zero
map `f`.  In clause (i), `E : Admissible A x y z`, `δ : Closed A z (S.obj 1 x)`
and `hδ` identify δ with the boundary of E under the shift Hom map, and
`K : Cone S E.a` is an arbitrary chosen cone.  The witnesses `e`, `t`, and
`H` have the source and target of the stated maps.  Their first two equations
are exactly `e = bρ` and `t = i s - σδ`; the next equation is `e t = 1`; the
following equation renders `te-1 = dH`; the next is `e i = b`; and the final
existential boundary witness renders `[-p] = [δe]` in H⁰.

Clause (ii) quantifies closed maps `f₁`, `f₂`, `a`, `b` and a degree-minus-one
`h` with `dh = b f₁ - f₂ a`, then arbitrary chosen cones `K₁`, `K₂`.  The
closed cone map `c` is followed by degree-minus-one witnesses for the two H⁰
class equalities `c i₁ = i₂ b` and `p₂ c = a[1] p₁`.  The final implication
expands “if `a` and `b` are homotopy equivalences” into closed inverse maps
and degree-minus-one witnesses for both inverse equations, and concludes with
an analogous inverse and two homotopies for `c`.

The declarations used are:

* `CategoryTheory.IntegralDGCategory` from
  `Sheaf.CategoryTheory.SmallDgCategory`;
* `CategoryTheory.IntegralDGCategory.ABC.Closed`, `Shifts`, `AxiomA`,
  `Admissible`, `boundary`, and `Cone` from `Sheaf.CategoryTheory.DgAbcData`.

Searches performed: the node's recorded LeanFinder, Loogle, LeanSearch, and
Mathlib grep searches were reviewed; they found only ordinary cochain-complex
mapping-cone APIs, not this arbitrary dg-category statement.  I additionally
ran `rg -n` over `WeilConjectures/`, the project `lean/Sheaf/`, and Mathlib for
`DGCategory`, `DifferentialGraded`, `admissible`, and cone-map terminology.
The only exact project interfaces were `SmallDgCategory` and `DgAbcData`, which
are reused.  No Mathlib or upstream declaration states this theorem.

Edge cases checked in the statement design include the empty object type (the
axiom-A hypothesis is retained), a zero object and zero cone, the zero map and
identity map, empty or degenerate admissible sequences, characteristic-free
integer signs including degree `-1`, and arbitrary choices of cone data and
splittings.  No triangulated structure is assumed.

## Second reading by Q141

I independently compared the node statement with `dg_abc_cone_homotopy`.  The
binders `A`, `S`, `hA`, and `hC` match the small dg category, shifts, axiom (A),
and cone existence assumptions.  Part (i) retains every object, admissible
sequence, shifted boundary witness, chosen cone, and all six conclusion clauses:
the degree-zero composites are rendered by `compZero`, while the two H⁰ equalities
are represented by explicit degree-minus-one differential witnesses.  Part (ii)
retains the homotopy-commutative square equation, arbitrary cones, both cone-map
class equalities, and the final implication; the implication expands both
homotopy equivalences into closed inverse maps and their two boundary equations,
and concludes with the corresponding inverse cone map and homotopies.  No
hypothesis or conclusion was added or omitted, and the module imports exactly the
landed interfaces used by the statement.  Compilation with `scompile.py` passed
without errors or warnings.
