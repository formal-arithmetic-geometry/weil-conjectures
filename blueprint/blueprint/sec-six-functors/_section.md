+++
id = "sec-six-functors"
kind = "section"
title = "Six Functors"
order = 2039
uses = ["sec-nagata-compactification", "sec-proper-base-change", "sec-smooth-base-change", "sec-smooth-purity"]
+++
content: the six operations, projection formulas, duality, and preservation
of constructible and finite-Tor categories.  
key theorem: Thm [sk-thm-sf-package].  
references: `six_functors_summary.tex`; the detailed source
`version/sketch/10b_six_functor_formalism.tex`.

**Source conventions.** Numbered chapter references and source
identifiers below refer to the expanded blueprint summarized by
`six_functors_summary.tex`, rather than to section numbers of this
merged document. Identifiers with targets in this document link to them;
other identifiers are printed as provenance labels. Statements described
as proved in earlier chapters refer to those detailed sources. The summary's
conditional hypotheses and split markers are retained.

The chapter is an *enumeration*: every property is either proved in an
earlier chapter of the blueprint — and is then restated here as a proposition
with its provenance, never as a definition — or is proved in this section, in
which case an idea-proof is given. The target is the *six-operations
package* consumed by the smooth-purity, Poincaré-duality, trace-formula and
final chapters.

This is the brief blueprint of the six-functor step. In the compiled
blueprint the six-functor chapter is a single long chapter whose opening
node axiomatizes the six operations and proves the formal core from the
axioms. Read as a *summary* the content is an enumeration, and that is
the form given here:

2pt
1. §§ *Objects and notation* fixes the objects and *only* the objects:
coefficient stages, *the ambient categories and their small
subcategories*, the six operations *with their source and target
categories*, the exchange and projection transformations, the admissibility
hypothesis and the orientation *interface*. Every descent of an
operation to a small category is a theorem, enumerated in a typing table
([sk-rem-sf-typing]): no preservation property is built into a definition.
1. §§ *What the earlier chapters prove* enumerates the properties that the earlier chapters
of the blueprint prove. Each is stated as a proposition with a proof that
names the statements proving it (compact-support base change, the
pro-étale comparison, finiteness, Künneth, existence of the exceptional
right adjoint, preservation for $Rf^!$, general biduality, and the four
independent statements of the trace layer). Four properties are *not* restated here, being proved in
this document: proper base change is [sk-thm-properbasechange]
(§[sec-proper-base-change]), smooth base change is
[sk-thm-smooth-base-change] (§[sec-smooth-base-change]), and the
compactification package is [sk-thm-nagata-compactification] together with
[sk-prop-nagata-sketch-comp-category]
(§[sec-nagata-compactification]) and the coherence, composition and
proper-coincidence statements of §§ *What this section proves*; and smooth purity is
[sk-thm-smooth-purity] with [sk-prop-cohsm] and
[sk-thm-purity-transport] (§[sec-smooth-purity]). All four are cited
directly. Nothing in this subsection is assumed: every one of them is a
theorem of this blueprint.
1. §§ *What this section proves* proves, in this section, the coherence of the
compact-support functor (refinement comparisons, the composition law, proper
coincidence), the projection formula at
every coefficient stage together with its coherence, the formal core, the
rotation of the input face of the duality theorems, the relative product
theorem, the stability of the finite-Tor subcategories, the two
finite-Tor cells (direct image, internal Hom), and the Künneth–Verdier
isomorphism with the exceptional and external-Hom comparisons it rests on. Each carries an idea-proof.
1. §§ *The final proposition* states the final proposition — the six-operations
package — and proves it by assembling the propositions of §§ *What the earlier chapters prove*
and §§ *What this section proves*; a dependency figure and a ledger of what is conditional
follow.

Separation of conclusions is respected: every node below is a separate
statement, and the steps that may split into very many statements carry a
qualitative **split marker**.
