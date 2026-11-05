"""Readable vector layouts for two commuting-map illustrations."""
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

ROOT = Path(__file__).resolve().parent

def box(ax, xy, title, width=.27):
    x,y=xy
    ax.add_patch(FancyBboxPatch((x-width/2,y-.065),width,.13,
                 boxstyle='round,pad=.012',facecolor='white',edgecolor='#334155'))
    ax.text(x,y,title,ha='center',va='center',fontsize=11)

def arrow(ax, a, b, label, text_xy):
    ax.add_patch(FancyArrowPatch(a,b,arrowstyle='-|>',mutation_scale=12,
                                color='#475569',linewidth=1.1))
    ax.text(*text_xy,label,ha='center',va='center',fontsize=10,
            bbox={'facecolor':'white','edgecolor':'none','pad':1.2})

fig,ax=plt.subplots(figsize=(6.6,3.5))
ax.set(xlim=(0,1),ylim=(0,1));ax.axis('off')
box(ax,(.5,.87),r'World $X$')
box(ax,(.2,.52),r'Fine output $O_F$')
box(ax,(.8,.52),r'Coarse output $O_C$')
arrow(ax,(.43,.80),(.23,.60),r'$\pi_F$',(.28,.75))
arrow(ax,(.57,.80),(.77,.60),r'$\pi_C$',(.72,.75))
arrow(ax,(.35,.52),(.65,.52),r'$c$',(.5,.59))
ax.text(.5,.36,r'$\pi_C=c\circ\pi_F$',ha='center',fontsize=11)
box(ax,(.2,.13),r'$X/{\sim_F}$')
box(ax,(.8,.13),r'$X/{\sim_C}$')
arrow(ax,(.35,.13),(.65,.13),'Induced surjection',(.5,.23))
for ext in ['pdf','svg']:fig.savefig(ROOT/'figures'/f'concept_interface_refinement.{ext}',bbox_inches='tight')
plt.close(fig)

fig,ax=plt.subplots(figsize=(6.6,3.3))
ax.set(xlim=(0,1),ylim=(0,1));ax.axis('off')
box(ax,(.22,.8),r'Extended $X_M\times H$',.36)
box(ax,(.22,.2),r'Base $X_M$',.36)
box(ax,(.8,.5),r'Observations $O$',.34)
arrow(ax,(.22,.72),(.22,.28),r'$p(x,h)=x$',(.32,.49))
arrow(ax,(.41,.23),(.66,.43),r'$\pi_M$',(.58,.25))
arrow(ax,(.41,.77),(.66,.57),r'$\pi_{M^H}$',(.58,.76))
ax.text(.58,.07,r'$\pi_{M^H}=\pi_M\circ p$',ha='center',fontsize=11)
for ext in ['pdf','svg']:fig.savefig(ROOT/'figures'/f'concept_hidden_extension.{ext}',bbox_inches='tight')
plt.close(fig)
