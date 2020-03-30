def parse(file_name):
    f = open(file_name, "r")
    lines = f.readlines()
    lines = [line.strip() for line in lines]
    lines = list(map(lambda line : clean_comments(line), lines))
    lines = list(filter(lambda line : clean_spaces_or_empty(line), lines))
    
    print(lines)
    return lines

comment_symbol = "#"
def clean_comments(line):
    comment_idx = line.find(comment_symbol)
    if comment_idx == -1:
        return line
    else:
        pre_comment = line[0:comment_idx]
        return pre_comment
        
        

spaces_or_empty = {"\n", "\t", " ", ""}
def clean_spaces_or_empty(line):
    return line not in spaces_or_empty
        


parse("assembly_ball_moving.txt")
    