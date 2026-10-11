## Worker report

The module `Sheaf.AlgebraicGeometry.SectionClearingDenominatorsQCQS` states
`AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_eq_restrict_qcqs`. It uses
`[CompactSpace X]` for quasi-compactness and `[QuasiSeparatedSpace X]` for
quasi-separatedness, then an invertible module `L`, a global section
`s : 𝟙_ X.Modules ⟶ L`, a quasi-coherent module `F`, and a section `t` on
`(Hom.zeroLocus s).support.compl`. Its conclusion is exactly the existence of
`m : ℕ` and `u : Γ(F ⊗ L.tensorPow m, ⊤)` whose restriction equals
`((ρ_ F).inv ≫ F ◁ tensorPowSection s m).app _ t`.

Dependencies used are Mathlib's `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.residueField` through the scheme/module infrastructure,
`AlgebraicGeometry.Scheme.Modules.IsInvertible` from
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`, and the project
quasi-coherent module notion `SheafOfModules.IsQuasicoherent` (the node
`pqf-def-coherent`'s quasi-coherent clause). The definitions `Hom.zeroLocus` and
`tensorPowSection` are imported from
`WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators`.

Edge cases checked: `m` is allowed to be zero; the nonvanishing locus may be empty,
so `t` is a section over the empty open; and no nonemptiness or positive-power
hypothesis is imposed on `L`, `F`, or `X`. The universes use one explicit `u`.

Searches made: `msearch.py leanfinder` with query “clearing denominators quasi coherent
invertible module qcqs scheme” found only structure-sheaf localization and no matching
invertible-module theorem; `msearch.py loogle` for `exists_tensorPowSection_eq_restrict`
found no hit; `msearch.py grep` for that name in AlgebraicGeometry found no exact
statement in the Sheaf project. A direct `rg` search found the stronger separated-over-
affine theorem `AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_eq_restrict`
in the slopmaster2 source, whose hypotheses do not match this qcqs statement, so this
separate declaration is required.

## Earlier second reading (a previous round; superseded)

The Lean binders match the node clause by clause: compactness and quasi-separatedness
are the two scheme hypotheses; `L` is invertible; `s` is a global section; `F` is
quasi-coherent; `t` is over the complement of the support of the zero locus, rendering
`X_s`; and the existential conclusion gives `m ≥ 0` via `m : ℕ`, a global section of
`F ⊗ L^{⊗m}`, and the stated restriction equality. No hypotheses or conclusion clauses
were added or omitted.

## Second reading by K1

I independently read the sandbox node and Lean module, all five statement-dependency
nodes, their declarations, and the source. The local Stacks tree is absent; I fetched
`https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex` into
`scratchpad/properties.tex` and read the section `section-principal-opens` and
`lemma-invert-s-sections` (lines 2227–2307, Tag 01PW). I also checked the rendered
[source](https://stacks.math.columbia.edu/tag/01PW). Part (2)'s surjectivity has exactly
the node's hypotheses; there is no standing base-field, separatedness, characteristic,
Noetherian or finite-type assumption. The node has no statement correction.

Object/hypothesis/conclusion checklist:

1. Scheme X: `variable {X : Scheme.{u}}`; Mathlib's `Scheme` extends a locally ringed
   space and requires local affine charts (`Scheme.lean:42`). Matches def-pc-scheme.
2. Quasi-compact X: `[CompactSpace X]`; `Topology/Defs/Filter.lean:283` requires
   compactness of the whole underlying space without any separation axiom. Matches
   def-weil-pbc-quasi-compact-scheme's mathlib_match.
3. Quasi-separated X: `[QuasiSeparatedSpace X]`;
   `quasiSeparatedSpace_iff_forall_affineOpens` (Morphisms/QuasiSeparated.lean:56)
   identifies this with compact intersections of affine opens. Exact, no separatedness
   or affine-intersection assumption.
4. Invertible O_X-module L: `(L : X.Modules) [L.IsInvertible]`. The recorded
   `Scheme.Modules.IsInvertible` (Modules/Invertible.lean:57) is local isomorphism
   with the structure sheaf, hence local rank one and quasi-coherent. This is the
   scheme-specific dependency declaration, not a new notion or extra hypothesis.
5. Global section s of L: `(s : 𝟙_ X.Modules ⟶ L)` is an O_X-linear map from O_X,
   determined by the image of 1, hence a global section. TensorSection's
   `unitSectionsEquiv` identifies the unit's sections with structure-sheaf sections.
6. Quasi-coherent O_X-module F: `(F : X.Modules)` and
   `[SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]`. I read Mathlib's
   Sheaf/Quasicoherent.lean:251 (local free presentations), the pqf-def-coherent
   dependency module Coherent.lean (which explicitly assigns its quasi-coherent
   clause to this Mathlib declaration), and upstream Modules/Tilde.lean:101–124
   (localization on affine charts). This is the same affine-local notion; the
   dependency's main declaration IsCoherent serves another clause, and is not an
   assumption here. No coherence or module finiteness is imposed.
7. X_s defined by nonzero residue-field value: `(Hom.zeroLocus s).support.compl`.
   I read ZeroLocus.lean:159–203: on a trivializing affine chart the ideal is (f)
   when s = f e, and its support is V(f), so its complement is D(f). Precisely
   f is outside the point's prime iff its residue-field value is nonzero.
   The domain O_X and target L are both invertible, so the documented junk case of
   zeroLocus cannot occur. The recorded `Scheme.residueField` is the stalk modulo
   its maximal ideal (Mathlib ResidueField.lean:45); no different fibre field is used.
8. Every local section u: `(t : Γ(F, (Hom.zeroLocus s).support.compl))`. Binder t
   names the node's u; it is universally quantified before the existential witnesses.
9. Exponent m >= 0: `∃ (m : ℕ)`, including zero, exactly the source's exponents.
10. Global section of F tensor L^m: `(u : Γ(F ⊗ L.tensorPow m, ⊤))`, where Lean u
    names the node's t. The tensor powers and unit convention are the existing ones.
11. Restriction equality: `.presheaf.map (homOfLE le_top).op u` restricts the global
    section to X_s. The right side
    `((ρ_ F).inv ≫ F ◁ tensorPowSection s m).app _ t` is tensoring t with s^m:
    I read tensorPowSection's recursion and
    `rightUnitor_inv_comp_whiskerLeft_app` (ClearDenominators.lean:154–160), whose
    equality with `tmulSection t (tensorPowSectionOne s m U)` confirms the formula.
    Both sides are in the same section module, without an added invertibility
    hypothesis on s. Every conclusion clause matches.

Edge cases: the empty scheme and empty affine cover are permitted (the proof can
choose a = b = 0 and the unique section). Empty X_s, including s = 0, is permitted;
sections over the empty open are unique and a zero global section satisfies the
conclusion. F = 0 is permitted. L = 0 is allowed exactly where it is invertible,
including the empty scheme. m = 0 uses the tensor unit and tensorPowSection s 0 = id.
There is no index binder, no nonempty or positive-exponent binder, and no restriction
on characteristic or commutative local rings. Universe u is explicitly declared and
arbitrary; there are no independent test-object universes and no unbound variables.

Independent searches used different terms from the first reader:
- msearch LeanSearch: "A section of a quasi coherent sheaf on the nonzero locus of a
  line bundle section extends after twisting by a power on a quasicompact
  quasiseparated scheme"; service returned Internal Server Error, recorded unavailable.
- msearch Loogle: `"QuasiSeparatedSpace"`; found the exact topological predicate and
  compact-open intersection statements, not this module-section theorem.
- msearch LeanFinder: "Extend a local section of a sheaf of modules after
  multiplication by a power of a line bundle section"; found tilde-module local
  fraction declarations and the structure-sheaf affine clearing statement, no match.
- msearch grep `denominator|tensorPowSection|nonvanishing` in Mathlib AlgebraicGeometry;
  only unrelated elliptic-curve denominators. Direct rg of the source project's
  AlgebraicGeometry/Modules and the repository's lean/Sheaf/AlgebraicGeometry found
  the separated-over-affine upstream clearing theorem and other nonvanishing-locus
  statements, no qcqs module-section theorem. I opened upstream
  exists_tensorPowSection_eq_restrict at ClearDenominators.lean:263–270: its explicit
  morphism to an affine base with IsSeparated is a stronger hypothesis, so it cannot
  be recorded as this statement. The full new declaration name has no source or
  upstream-name-table collision.

Repair: H8, the original theorem docstring only named broad proof techniques. I
replaced that sentence with the node's three complete proof steps and dependency
ids: simultaneous affine charts and local fractions with a common exponent;
quasi-compact overlaps, quasi-coherent twists and restriction torsion; a common
additional exponent and sheaf gluing. I also removed the duplicated blueprint
markers and made each source marker a single complete citation. No mathematical
signature or node statement changed. There are no new nodes or dependency modules,
no hollow definitions, and the only theorem's proof remains `by sorry`. The existing
imports supply quasi-separatedness, clearing-denominator tensor operations and the
module/sheaf infrastructure. The lean.statement record is unchanged and verbatim
matches the signature, with whitespace normalized.

Validation: scompile.py compiled the repaired module on the server in 2.3 seconds,
exit code 0, without warnings. stage2_delivery.py signature reproduced the unchanged
lean.statement exactly; the line-width check found no Lean line over 100 characters.
