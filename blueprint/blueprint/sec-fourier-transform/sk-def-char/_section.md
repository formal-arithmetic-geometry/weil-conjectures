+++
id = "sk-def-char"
kind = "section"
title = "Additive characters"
order = 2671
lean = ["AddChar.FiniteField.primitiveChar"]
uses = ["sk-def-fourier-set"]
+++
*Definition (sketch).*

A *nondegenerate additive character* of $k$ (finite or algebraically
closed of characteristic $p$) is a nontrivial homomorphism
$\psi:(k,+)\to\Qlb^\times$. For $k_0=\Fq$ and a fixed nontrivial
$\Psi:\Fp\to\Qlb^\times$, the character
$\psi(x)=\Psi(\Tr_{k_0/\Fp}(x))$ is *the* nondegenerate additive
character; $\psi_a(x)=\psi(ax)$, $a\in k_0^\times$, runs through all of them
(*note: this parametrization seems never to be used later — only the
fixed $\psi$, its scalings $\psi_a$ and $\psi^{-1}=\psi_{-1}$ occur — so it
has no detailed counterpart in the blueprint*);
over $\mathbf F_{q^n}$ one writes
$\psi_n(x)=\psi(\Tr_{\mathbf F_{q^n}/k_0}(x))=\Psi(\Tr_{\mathbf F_{q^n}/\Fp}(x))$. (Blueprint the Fourier–Deligne chapter,
def:fd-additive-character.)

Uses: [sk-def-fourier-set]
